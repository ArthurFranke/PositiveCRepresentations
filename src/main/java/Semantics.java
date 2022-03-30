import org.tweetyproject.logics.cl.syntax.ClBeliefSet;
import org.tweetyproject.logics.cl.syntax.Conditional;
import org.tweetyproject.logics.pl.sat.SatSolver;
import org.tweetyproject.logics.pl.semantics.NicePossibleWorld;
import org.tweetyproject.logics.pl.syntax.Conjunction;
import org.tweetyproject.logics.pl.syntax.Implication;
import org.tweetyproject.logics.pl.syntax.Negation;
import org.tweetyproject.logics.pl.syntax.PlFormula;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Set;

public class Semantics {

    public static boolean tolerates(Conditional conditional, ClBeliefSet beliefSet){
        Collection<PlFormula> premise = conditional.getPremise();
        PlFormula conclusion = conditional.getConclusion();
        Conjunction conjunction = new Conjunction(CollectionToConjunction(premise), conclusion);

        for (Conditional c : beliefSet) {
            Implication implication = new Implication (CollectionToConjunction(c.getPremise()), c.getConclusion());
            conjunction.add(implication);
        }

        SatSolver solver = SatSolver.getDefaultSolver();
        return solver.isConsistent((Collection<PlFormula>) conjunction);
    }

    public static ArrayList<ClBeliefSet> getPartitions(ClBeliefSet delta){
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

    public static ArrayList<NicePossibleWorld> getVerifyingWorlds(Conditional c, Set<NicePossibleWorld> worlds){
        ArrayList<NicePossibleWorld> vWorlds = new ArrayList<>();
        Conjunction conjunction = new Conjunction(CollectionToConjunction(c.getPremise()), c.getConclusion());

        for(NicePossibleWorld w: worlds){
            if(w.satisfies((Collection<PlFormula>) conjunction)){
                vWorlds.add(w);
            }
        }
        return vWorlds;
    }

    public static ArrayList<NicePossibleWorld> getFalsifyingWorlds(Conditional c, Set<NicePossibleWorld> worlds) {
        ArrayList<NicePossibleWorld> fWorlds = new ArrayList<>();
        Negation nB = new Negation(c.getConclusion());
        Conjunction conjunction = new Conjunction(CollectionToConjunction(c.getPremise()), nB);

        for(NicePossibleWorld w: worlds){
            if(w.satisfies((Collection<PlFormula>) conjunction)){
                fWorlds.add(w);
            }
        }
        return fWorlds;
    }

    /* CollectionToConjunction */
    /* Compiles a collection of formulas into a conjunction */
    /* (used to compile premisses of conditionals into formulas) */
    public static Conjunction CollectionToConjunction(Collection<PlFormula> collection) {
        Conjunction conjunction = new Conjunction();
        conjunction.addAll(collection);
        return conjunction;
    }


    public static ArrayList<NicePossibleWorld> getOrderedList(Set<NicePossibleWorld> input){
        return null;
    }
}
