import org.tweetyproject.logics.cl.semantics.ConditionalStructure;
import org.tweetyproject.logics.cl.syntax.ClBeliefSet;
import org.tweetyproject.logics.cl.syntax.Conditional;
import org.tweetyproject.logics.pl.sat.Sat4jSolver;
import org.tweetyproject.logics.pl.sat.SatSolver;
import org.tweetyproject.logics.pl.semantics.NicePossibleWorld;
import org.tweetyproject.logics.pl.syntax.Conjunction;
import org.tweetyproject.logics.pl.syntax.Negation;
import org.tweetyproject.logics.pl.syntax.PlFormula;

import java.util.*;

public class PosCRep {
    private static final Integer MAX_VAL = Integer.MAX_VALUE;
    private static ArrayList<int[]> impacts = new ArrayList<>();
    private static Set<NicePossibleWorld> worlds;
    private static ArrayList<ClBeliefSet> partitions;
    private static ArrayList<ConditionalKappa> condStruct;
    private static LinkedHashMap<NicePossibleWorld, Integer> kappaWorlds;
    private static LinkedHashMap<NicePossibleWorld, String> kappaWorlds2;
    private static HashSet<int[]> allImpacts;
    private static int kappa_0;
    private static int cRepType;

    public static void main(String[] args) {
        SatSolver.setDefaultSolver(new Sat4jSolver());
        condStruct = new ArrayList<>();
        kappaWorlds = new LinkedHashMap<>();
        kappaWorlds2 = new LinkedHashMap<>();
        allImpacts = new HashSet<>();

        /* set knowledgebase */
        KnowledgeBases kbHat = new KnowledgeBases();
        kbHat.setKnowledgeBase();

        /* set knowledgebase for which the cRep are computed */
        ClBeliefSet delta = kbHat.getPenguin();

        /* set which cRep should be computed */
        /* 0 = simple, 1 = reward-fix, 2 = fair */
        cRepType = 2;

        /* generate partitions and worlds */
        partitions = Semantics.getPartitions(delta);
        worlds = NicePossibleWorld.getAllPossibleWorlds(delta.getSignature().toCollection());

        ConditionalStructure cs = new ConditionalStructure(delta);

        /* check for consistency */
        if(partitions.isEmpty()){
            inconsistentErrorMessage();
        }
        else{
            /* get all negative impact-values */
            ImpactGenerator iGenerator = new ImpactGenerator(delta.size(),9);
            impacts = iGenerator.generateCombinations();

            setKappaValues(delta);
            setKappaWorlds(delta);

            int index = 0;

            /* check if generated function is an cRep */
            boolean test = testCorrectness();

            if(!test){
                /* remove impact-values, which lead to no cRep */
                impacts.remove(0);

                /* search as long there are possible impact-values */
                while(!test && impacts.size() > 0) {
                    setKappaValues(delta);
                    setKappaWorlds(delta);
                    System.out.println(index);
                    index++;
                    test = testCorrectness();
                    impacts.remove(0);
                }
            }
            if(impacts.size()>0){
                printResults(delta,cs);
                System.out.println("+++++++++++++++++++++++++++++++++++++++++++++");
            }
            else{
                System.out.println("+++++++++++++++++++++++++++++++++++++++++++++");
                System.out.println("No c-representation was found!");
            }
        }
    }

    private static void setKappaValues(ClBeliefSet kb) {
        condStruct.clear();
        kappaWorlds.clear();

        int kappaMinus;
        int kappaPlus;
        int index = 0;

        for(Conditional conditional : kb){
            kappaMinus = impacts.get(0)[index];

            if(cRepType == 0){
                kappaPlus = 0;
            } else if(cRepType == 1){
                kappaPlus = 1;
            } else {
                kappaPlus = -1 * kappaMinus;
            }

            index++;
            condStruct.add(new ConditionalKappa(conditional,kappaMinus, kappaPlus));
        }
    }

    private static void setKappaWorlds(ClBeliefSet kb) {
        int kappa;
        ArrayList<Conditional> kbList = new ArrayList<>(kb);

        for(NicePossibleWorld w: worlds) {
            // initial value of kappa_zero is 0, can be changed if necessary
            // but shouldn't happen since the following methods adjust it
            kappa = 0;
            String kappa_values= "";
            for(Conditional c: kbList){

                PlFormula con = c.getConclusion();
                Conjunction pre = Semantics.CollectionToConjunction(c.getPremise());
                Negation negCon = new Negation(con);

                int index = 0;
                for(ConditionalKappa cK : condStruct){
                    if(cK.getConditional().equals(c)) index = condStruct.indexOf(cK);
                }

                if(w.satisfies((Collection<PlFormula>) pre.combineWithAnd(con))){
                    kappa = kappa + condStruct.get(index).getKappaPos();
                    kappa_values = kappa_values.concat("k_" + (kbList.indexOf(c)+1) + "^+ (" + c + "), ");

                }
                if(w.satisfies((Collection<PlFormula>) pre.combineWithAnd(negCon))){
                    kappa = kappa + condStruct.get(index).getKappaNeg();
                    kappa_values = kappa_values.concat("k_" + (kbList.indexOf(c)+1) + "^- (" + c + "), ");
                }
            }
            kappaWorlds.put(w,kappa);
            kappaWorlds2.put(w,kappa_values);

        }
    }

    /* check the inequationssystem*/
    private static boolean testCorrectness(){
        boolean result = true;
        ArrayList<Integer> negativeNumbers = new ArrayList<>();

        for(int k : kappaWorlds.values()){
            if(k<0){
                negativeNumbers.add(k);}
        }
        // for negative kappa values adjust kappa_0 accordingly
        if(!negativeNumbers.isEmpty()){
            kappa_0 = Math.abs(Collections.min(negativeNumbers));
            kappaWorlds.replaceAll((w, v) -> v + kappa_0);
        }

        // if there is only positive numbers, but no zero
        if(!kappaWorlds.containsValue(0)){
            kappa_0 = Collections.min(kappaWorlds.values());
            kappaWorlds.replaceAll((w, v) -> v - kappa_0);
        }


        if(kappaWorlds.containsValue(0)){
            Iterator<ConditionalKappa> it = condStruct.iterator();

            int kappaPosSum;
            int kappaNegSum;

            while(result && it.hasNext()){
                ConditionalKappa cK = it.next();
                Conditional k = cK.getConditional();

                ArrayList<NicePossibleWorld> vWorlds = Semantics.getVerifyingWorlds(k, worlds);
                ArrayList<NicePossibleWorld> fWorlds = Semantics.getFalsifyingWorlds(k, worlds);

                ArrayList<Integer> possibleMinimaW = new ArrayList<>();
                ArrayList<List<Integer>> possibleMinimaW_details = new ArrayList<>();
                ArrayList<Integer> possibleMinimaF = new ArrayList<>();
                ArrayList<List<Integer>> possibleMinimaF_details = new ArrayList<>();

                for (NicePossibleWorld w : vWorlds) {
                    kappaPosSum = getKappaSum(k, w, true);
                    kappaNegSum = getKappaSum(k, w, false);
                    possibleMinimaW.add(kappaPosSum + kappaNegSum);
                    List<Integer> arr = Arrays.asList(kappaPosSum, kappaNegSum);
                    possibleMinimaW_details.add(arr);
                }
                for (NicePossibleWorld w : fWorlds) {
                    kappaPosSum = getKappaSum(k, w, true);
                    kappaNegSum = getKappaSum(k, w, false);
                    possibleMinimaF.add(kappaPosSum + kappaNegSum);
                    List<Integer> arr = Arrays.asList(kappaPosSum, kappaNegSum);
                    possibleMinimaF_details.add(arr);
                }

                int rightSum = Collections.min(possibleMinimaW) - Collections.min(possibleMinimaF);
                if (cK.getKappaDiff() <= rightSum) {
                    result = false;
                    kappa_0 = 0;
                }
                /*
                System.out.println(k + " :" + vWorlds + ", " + fWorlds);

                System.out.println(k + " :" + cK.getKappaDiff() + " > " +
                        possibleMinimaW_details  +" - " +
                        possibleMinimaF_details +" = " +
                        Collections.min(possibleMinimaW) +" - " +
                        Collections.min(possibleMinimaF)
                );
                */
            }
        }
        return result;
    }

    private static int getKappaSum(Conditional c, NicePossibleWorld w, Boolean flag) {
        ArrayList<Integer> kappaList = new ArrayList<>();
        ArrayList<ConditionalKappa> varCondStruct = new ArrayList<>(condStruct);

        varCondStruct.removeIf(cK -> cK.getConditional().equals(c));

        for(ConditionalKappa cK : varCondStruct){
            Conditional k = cK.getConditional();
            if(flag){
                Conjunction ab = new Conjunction(Semantics.CollectionToConjunction(k.getPremise()), k.getConclusion());
                if (w.satisfies((Collection<PlFormula>) ab)) {
                    kappaList.add(cK.getKappaPos());
                }
            }
            else {
                Negation nb = new Negation(k.getConclusion());
                Conjunction anb = new Conjunction(Semantics.CollectionToConjunction(k.getPremise()), nb);
                if(w.satisfies((Collection<PlFormula>) anb))
                    kappaList.add(cK.getKappaNeg());
            }
        }
        int sum = 0;
        for(Integer i : kappaList) sum+=i;
        return sum;
    }

    public static int getRandomNumberInRange(int min, int max) {
        Random r = new Random();
        OptionalInt value = r.ints(min, (max + 1)).limit(1).findFirst();
        return value.isPresent() ? value.getAsInt() : 0;
    }

    public static void printResults(ClBeliefSet delta, ConditionalStructure cs) {
        // Printing all details

        System.out.println("\n\n--------------------------");
        System.out.println("Knowledgebase:");
        System.out.println("--------------------------");
        System.out.println("Delta = " + delta + "\n");
        System.out.println("--------------------------");

        System.out.println("Partitioning:");
        System.out.println("--------------------------");
        int l = 0;
        for(ClBeliefSet bs : partitions){
            System.out.println("Delta_" + l + " = " + bs);
            l++;
        }
        System.out.println(" ");
        System.out.println("--------------------------");
        System.out.println("Impact-factors:");
        System.out.println("--------------------------");
        for(ConditionalKappa cK : condStruct){
            System.out.println(cK);
        }
        if(kappa_0 != 0) {
            System.out.println("\nKappa_0 had to be adjusted to: " + kappa_0);
        }
        System.out.println(" ");
        System.out.println("--------------------------");
        System.out.println("c-representation of Delta:");
        System.out.println("--------------------------");

        Set<NicePossibleWorld> omega = cs.getPossibleWorlds();

        for (NicePossibleWorld o : omega) {
            System.out.println(o + " = " + kappaWorlds.get(o) + " : " + kappaWorlds2.get(o));
        }
    }

    public static void inconsistentErrorMessage() {
        System.out.println("* * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *");
        System.out.println("* \t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t  *");
        System.out.println("* \t The given knowledge base is inconsistent. Please check your input. \t  *");
        System.out.println("* \t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t  *");
        System.out.println("* * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *");
    }



    private void localToGlobalWorlds(ArrayList<ClBeliefSet> cliques){
        LinkedHashMap<NicePossibleWorld, ArrayList<Integer>> result;
        ArrayList<Integer> tmp_values = new ArrayList<>();
    }
}
