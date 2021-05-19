import org.tweetyproject.logics.cl.syntax.ClBeliefSet;
import org.tweetyproject.logics.cl.syntax.Conditional;
import org.tweetyproject.logics.pl.sat.Sat4jSolver;
import org.tweetyproject.logics.pl.sat.SatSolver;
import org.tweetyproject.logics.pl.semantics.NicePossibleWorld;
import org.tweetyproject.logics.pl.syntax.Conjunction;
import org.tweetyproject.logics.pl.syntax.Negation;
import org.tweetyproject.logics.pl.syntax.PlFormula;
import org.tweetyproject.logics.pl.syntax.Proposition;

import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.PrintStream;
import java.util.*;

public class ExperimentalSearch {
    private static Set<NicePossibleWorld> worlds;
    private static ArrayList<ClBeliefSet> partitions;
    private static ArrayList<ConditionalKappa> condStruct;
    private static Map<NicePossibleWorld, Integer> kappaWorlds;

    public static void main(String[] args) {

        // If the Ouput should be printed in a seperate file instead of the terminal
        // throws FileNotFoundException
        // PrintStream out = new PrintStream(new FileOutputStream("output1.txt"));
        // System.setOut(out);

        SatSolver.setDefaultSolver(new Sat4jSolver());
        condStruct = new ArrayList<>();
        kappaWorlds = new HashMap<>();

        /* Define knowledgebase */
        ArrayList<ClBeliefSet> knowledgeBases = setKnowledgeBase();
        ClBeliefSet delta = knowledgeBases.get(0); //pick between 0 and 2

        partitions = Semantics.getPartitions(delta);
        worlds = NicePossibleWorld.getAllPossibleWorlds(delta.getSignature().toCollection());

        if(partitions.isEmpty()){
            PositiveCRepresentation.inconsistentErrorMessage();
        }
        else{
            for(int i = 0; i<1000000; i++){
                setKappaValuesRandomly(delta);
                setKappaWorlds(delta);

                if(testCorrectness()){
                    System.out.println("\n* * * * * * * * * * * * * * *");
                    System.out.println("Impact-factors:");
                    for(ConditionalKappa cK : condStruct){
                        System.out.println(cK);
                    }
                    kappaWorlds.forEach((k, v)-> System.out.println(k + ": " + v));
                }
            }
        }
    }

    private static void setKappaValuesRandomly(ClBeliefSet delta) {
        condStruct.clear();
        kappaWorlds.clear();
        int kappaMinus;
        int kappaPlus;

        for(Conditional c : delta) {
            kappaMinus = PositiveCRepresentation.getRandomNumberInRange(-9,9);
            kappaPlus  = -1; //PositiveCRepresentation.getRandomNumberInRange(-9,9);

            condStruct.add(new ConditionalKappa(c, kappaMinus, kappaPlus));
        }
    }
    private static void setKappaValuesDifference(ClBeliefSet delta) {
        condStruct.clear();
        kappaWorlds.clear();
        int kappaMinus;
        int kappaPlus;

        for(Conditional c : delta) {
            kappaMinus = PositiveCRepresentation.getRandomNumberInRange(-10,10);
            kappaPlus  = PositiveCRepresentation.getRandomNumberInRange(-10,10);

            while((kappaMinus - kappaPlus) != 2){
                kappaMinus = PositiveCRepresentation.getRandomNumberInRange(1,10);
                kappaPlus  = PositiveCRepresentation.getRandomNumberInRange(1,10);
            }
            condStruct.add(new ConditionalKappa(c, kappaMinus, kappaPlus));
        }
    }

    private static void setKappaValuesPartition(ClBeliefSet kb) {
        condStruct.clear();
        kappaWorlds.clear();

        int kappaMinus;
        int kappaPlus = 1;

        for(ClBeliefSet bs : partitions){
            boolean first_conditional = true;
            int i = partitions.indexOf(bs);

            for(Conditional cond: bs){
                kappaMinus = PositiveCRepresentation.getRandomNumberInRange(kappaPlus+1,10);

                if(first_conditional){
                    kappaMinus = (int) Math.pow(2, i+1);
                    first_conditional = false;
                }

                condStruct.add(new ConditionalKappa(cond,kappaMinus, kappaPlus));
            }
        }
    }

    public static void setKappaWorlds(ClBeliefSet kb) {
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

    private static boolean testCorrectness(){
        boolean result = true;
        int negativeNumbers = 0;
        for(int k : kappaWorlds.values()){
            if(k<0){
                negativeNumbers++;}
        }
        /*
        if(negativeNumbers > 0){
            result = false;
        }
        if(result &&
        */
        if(kappaWorlds.containsValue(0)){
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

    public static int getKappaSum(Conditional c, NicePossibleWorld w, Boolean flag) {
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

    private static ArrayList<ClBeliefSet> setKnowledgeBase(){
        ArrayList<ClBeliefSet> bases = new ArrayList<>();
        ClBeliefSet kb1 = new ClBeliefSet();

        /* Define signature */
        Proposition b = new Proposition("b"); //bird
        Proposition f = new Proposition("f"); //flying
        Proposition p = new Proposition("p"); //penguin
        Proposition w = new Proposition("w"); //winged animal
        Proposition k = new Proposition("k"); //kiwi

        Proposition a = new Proposition("a"); //awesome kiwi
        Proposition c = new Proposition("c"); //crocodile
        Proposition d = new Proposition("d"); //descend from dinosaurs

        Proposition e = new Proposition("e"); //lays eggs
        Proposition h = new Proposition("h"); //huge animal
        Proposition s = new Proposition("s"); //super-penguin

        /* Add Conditionals */
        kb1.add(new Conditional(b,f));
        kb1.add(new Conditional(p,b));
        kb1.add(new Conditional(p,new Negation(f)));
        kb1.add(new Conditional(b,w));

        /* super-penguins can fly */
        ClBeliefSet kb2 = new ClBeliefSet(kb1);
        kb2.add(new Conditional(s,p));
        kb2.add(new Conditional(s,f));

        /* knowledge about animals which lay eggs and new knowledge about crocodiles*/
        ClBeliefSet kb3 = new ClBeliefSet(kb2);
        kb3.add(new Conditional(e,p));
        kb3.add(new Conditional(e,d));
        kb3.add(new Conditional(h,c));
        kb3.add(new Conditional(c,d));

        //kb3.add(new Conditional(b,p)); // makes the knowledgebases inconsistent, for check purposes

        bases.add(kb1); // has two partitions and four conditionals
        bases.add(kb2); // has three partitions and six conditionals
        bases.add(kb3); // has three partitions and ten conditionals
        return bases;
    }
}
