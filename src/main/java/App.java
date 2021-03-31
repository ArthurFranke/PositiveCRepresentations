import org.tweetyproject.logics.cl.syntax.ClBeliefSet;
import org.tweetyproject.logics.cl.syntax.Conditional;
import org.tweetyproject.logics.pl.sat.Sat4jSolver;
import org.tweetyproject.logics.pl.sat.SatSolver;
import org.tweetyproject.logics.pl.semantics.PossibleWorld;
import org.tweetyproject.logics.pl.syntax.*;

import java.util.*;

public class App {

    private static ArrayList<ClBeliefSet> partitions;
    private static Set<PossibleWorld> worlds;
    private static HashMap<Conditional, ConditionalKappa> condStruct;
    private static HashMap<PossibleWorld, Integer> kappaWorlds;
    private static int KAPPA_NULL;

    public static void main(String[] args) {
        SatSolver.setDefaultSolver(new Sat4jSolver());

        ClBeliefSet delta = defineKnowledgeBase();
        partitions = getPartitions(delta);
        worlds = PossibleWorld.getAllPossibleWorlds(delta.getSignature());

    }

    private static ClBeliefSet defineKnowledgeBase(){
        ClBeliefSet kb = new ClBeliefSet();

        /* Define signature */
        Proposition b = new Proposition("b"); //bird
        Proposition f = new Proposition("f"); //can fly
        Proposition p = new Proposition("p"); //penguin
        Proposition w = new Proposition("w"); //has wings
        Proposition k = new Proposition("k"); //kiwis

        Proposition a = new Proposition("a"); //awesome kiwis
        Proposition c = new Proposition("c"); //crocodile
        Proposition d = new Proposition("d"); //descends from dinosaurs

        Proposition e = new Proposition("e"); //lays eggs
        Proposition h = new Proposition("h"); //is huge
        Proposition s = new Proposition("s"); //super-penguins

        kb.add(new Conditional(b,f));
        kb.add(new Conditional(p,b));

        kb.add(new Conditional(p,new Negation(f)));
        kb.add(new Conditional(b,w));

        return kb;
    }

    /* CollectionToConjunction */
    /* Compiles a collection of formulas into a conjunction */
    /* (used to compile premisses of conditionals into formulas) */
    private static Conjunction CollectionToConjunction(Collection<PlFormula> collection) {
        Conjunction conjunction = new Conjunction();
        conjunction.addAll(collection);
        return conjunction;
    }

    private static int getRandomNumberInRange(int min, int max) {
        Random r = new Random();
        OptionalInt value = r.ints(min, (max + 1)).limit(1).findFirst();
        return value.isPresent() ? value.getAsInt() : 0;
    }


    private static boolean tolerates(Conditional conditional, ClBeliefSet beliefSet){
        /* Generate formula for SAT-test */
        Conjunction conjunction = new Conjunction(CollectionToConjunction(conditional.getPremise()), conditional.getConclusion());

        for (Conditional cond:beliefSet) {
            Implication implication = new Implication (CollectionToConjunction(cond.getPremise()), cond.getConclusion());
            conjunction.add(implication);
        }

        return SatSolver.getDefaultSolver().isConsistent((Collection<PlFormula>) conjunction);
    }

    private static ArrayList<ClBeliefSet> getPartitions (ClBeliefSet delta){
        ClBeliefSet beliefSet = delta.clone();
        ArrayList<ClBeliefSet> deltaPartition = new ArrayList<>();

        boolean halt = false;

        while(!beliefSet.isEmpty() && !halt){
            halt = true;
            ClBeliefSet bsClone = beliefSet.clone();
            ClBeliefSet partition = new ClBeliefSet();

            for (Conditional conditional : beliefSet) {
                if (tolerates(conditional, bsClone)) {
                    partition.add(conditional);
                    halt = false;
                }
            }
            deltaPartition.add(partition);
            beliefSet.removeAll(partition);
            if(halt){
                deltaPartition.clear();
            }
        }
        return deltaPartition;
    }
}
