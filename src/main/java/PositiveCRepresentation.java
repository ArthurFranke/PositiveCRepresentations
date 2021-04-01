import org.tweetyproject.logics.cl.syntax.ClBeliefSet;
import org.tweetyproject.logics.cl.syntax.Conditional;
import org.tweetyproject.logics.pl.sat.Sat4jSolver;
import org.tweetyproject.logics.pl.sat.SatSolver;
import org.tweetyproject.logics.pl.semantics.NicePossibleWorld;
import org.tweetyproject.logics.pl.syntax.*;

import java.util.*;

public class PositiveCRepresentation {
    private static Set<NicePossibleWorld> worlds;
    private static ArrayList<ClBeliefSet> partitions;
    private static ArrayList<ConditionalKappa> condStruct;
    private static Map<NicePossibleWorld, Integer> kappaWorlds;

    public static void main(String[] args) {
        SatSolver.setDefaultSolver(new Sat4jSolver());
        condStruct = new ArrayList<>();
        kappaWorlds = new HashMap<>();

        ClBeliefSet delta = setKnowledgeBase();
        partitions = Semantics.getPartitions(delta);
        worlds = NicePossibleWorld.getAllPossibleWorlds(delta.getSignature().toCollection());

        setKappaValues(delta);
        setKappaWorlds(delta);

        while(!testCorrectness()){
            setKappaValues(delta);
            setKappaWorlds(delta);
        }

        printResults(delta);
    }

    private static ClBeliefSet setKnowledgeBase(){
        ClBeliefSet kb = new ClBeliefSet();

        /* Define signature */
        Proposition b = new Proposition("b"); //bird
        Proposition f = new Proposition("f"); //flying
        Proposition p = new Proposition("p"); //penguin
        Proposition w = new Proposition("w"); //winged animal
        Proposition k = new Proposition("k"); //kiwis

        Proposition a = new Proposition("a"); //awesome kiwis
        Proposition c = new Proposition("c"); //crocodile
        Proposition d = new Proposition("d"); //descends from dinosaurs

        Proposition e = new Proposition("e"); //lays eggs
        Proposition h = new Proposition("h"); //huge animal
        Proposition s = new Proposition("s"); //super-penguins

        kb.add(new Conditional(b,f));
        kb.add(new Conditional(p,b));

        kb.add(new Conditional(p,new Negation(f)));
        kb.add(new Conditional(b,w));


        return kb;
    }

    private static void setKappaValues(ClBeliefSet kb) {
        condStruct.clear();
        kappaWorlds.clear();

        int signature_length = kb.getSignature().size();
        int kappaMinus;
        int kappaPlus = 1;


        for(ClBeliefSet bs : partitions){
            boolean first_conditional = true;

            int i = partitions.indexOf(bs);

            for(Conditional cond: bs){
                kappaMinus = getRandomNumberInRange(signature_length+1);

                if(first_conditional){
                    kappaMinus = (int) Math.pow(2, i+1);
                    first_conditional = false;
                }

                condStruct.add(new ConditionalKappa(cond,kappaMinus, kappaPlus));
            }
        }
    }

    private static void setKappaWorlds(ClBeliefSet kb) {
        int kappa;
        for(NicePossibleWorld w: worlds) {
            // initial value of kappa_zero is 0, can be changed if necessary
            kappa = 0;
            for(Conditional c: kb){
                PlFormula con = c.getConclusion();
                Conjunction pre = Semantics.CollectionToConjunction(c.getPremise());
                Negation negCon = new Negation(con);

                int index = 0;
                for(ConditionalKappa cK : condStruct){
                    if(cK.getConditional().equals(c)) index = condStruct.indexOf(cK);
                }

                if(w.satisfies((Collection<PlFormula>) pre.combineWithAnd(con))){
                    kappa = kappa + condStruct.get(index).getKappaPos();
                }
                if(w.satisfies((Collection<PlFormula>) pre.combineWithAnd(negCon))){
                    kappa = kappa + condStruct.get(index).getKappaNeg();
                }
            }
            kappaWorlds.put(w,kappa);
        }
    }

    /* check */
    private static boolean testCorrectness(){
        boolean result = true;
        int negativeNumbers = 0;
        for(int k : kappaWorlds.values()){
            if(k<0){
                negativeNumbers++;}
        }
        if(negativeNumbers > 0){
            result = false;
        }
        if(result && kappaWorlds.containsValue(0)){
            Iterator<ConditionalKappa> it = condStruct.iterator();
            int kappaW;
            int kappaPosSum;
            int kappaNegSum;

            while(result && it.hasNext()){
                ConditionalKappa cK = it.next();
                Conditional k = cK.getConditional();

                ArrayList<NicePossibleWorld> vWorlds = Semantics.getVerifyingWorlds(k, worlds);
                ArrayList<NicePossibleWorld> fWorlds = Semantics.getFalsifyingWorlds(k, worlds);

                ArrayList<Integer> possibleMinimaW = new ArrayList<>();
                ArrayList<Integer> possibleMinimaF = new ArrayList<>();

                for (NicePossibleWorld w : vWorlds) {
                    kappaW = kappaWorlds.get(w);
                    kappaPosSum = getKappaSum(k, w, true);
                    kappaNegSum = getKappaSum(k, w, false);
                    possibleMinimaW.add(kappaW + kappaPosSum + kappaNegSum);
                }
                for (NicePossibleWorld w : fWorlds) {
                    kappaW = kappaWorlds.get(w);
                    kappaPosSum = getKappaSum(k, w, true);
                    kappaNegSum = getKappaSum(k, w, false);
                    possibleMinimaF.add(kappaW + kappaPosSum + kappaNegSum);
                }
                int rightSum = Collections.min(possibleMinimaW) - Collections.min(possibleMinimaF);
                if (cK.getKappaDiff() <= rightSum) {
                    result = false;
                }

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
        for(Integer i : kappaList) sum=+i;
        return sum;
    }


    private static int getRandomNumberInRange(int max) {
        Random r = new Random();
        int min = 2;
        OptionalInt value = r.ints(min, (max + 1)).limit(1).findFirst();
        return value.isPresent() ? value.getAsInt() : 0;
    }

    private static void printResults(ClBeliefSet delta) {
        // Printing all details
        System.out.println("Wissensbasis:\n" + "Delta = " + delta + "\n");

        System.out.println("Partionierung:");
        int l = 0;
        for(ClBeliefSet bs : partitions){
            System.out.println("Delta_" + l + " = " + bs);
            l++;
        }
        System.out.println("\nImpactfaktoren:");
        for(ConditionalKappa cK : condStruct){
            System.out.println(cK);
        }
        System.out.println("\nInduzierte c-Repraesentation:");
        kappaWorlds.forEach((k, v)-> System.out.println(k + ": " + v));
    }
}
