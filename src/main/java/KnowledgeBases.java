import org.tweetyproject.logics.cl.syntax.ClBeliefSet;
import org.tweetyproject.logics.cl.syntax.Conditional;
import org.tweetyproject.logics.pl.syntax.Conjunction;
import org.tweetyproject.logics.pl.syntax.Negation;
import org.tweetyproject.logics.pl.syntax.Proposition;
import org.tweetyproject.logics.pl.syntax.Tautology;

import java.util.ArrayList;

public class KnowledgeBases {

    ClBeliefSet chain = new ClBeliefSet();

    ClBeliefSet chainLonger = new ClBeliefSet();

    ClBeliefSet chainLonger_c1 = new ClBeliefSet();
    ClBeliefSet chainLonger_c2 = new ClBeliefSet();
    ClBeliefSet chainLonger_c3 = new ClBeliefSet();

    ClBeliefSet circle = new ClBeliefSet();
    ClBeliefSet starPre = new ClBeliefSet();
    ClBeliefSet starCon = new ClBeliefSet();

    ClBeliefSet penguin = new ClBeliefSet();
    ClBeliefSet penguin_z0 = new ClBeliefSet();
    ClBeliefSet penguin_z1 = new ClBeliefSet();

    ClBeliefSet penguin_c1 = new ClBeliefSet();
    ClBeliefSet penguin_c2 = new ClBeliefSet();

    ClBeliefSet thesis = new ClBeliefSet();
    ClBeliefSet thesis_c1 = new ClBeliefSet();
    ClBeliefSet thesis_c2 = new ClBeliefSet();
    ClBeliefSet thesis_c3 = new ClBeliefSet();

    ClBeliefSet carstart = new ClBeliefSet();
    public KnowledgeBases() {
        // empty Constructor
    }

    /*
     *  A simple Method for preloading some knowledgebases
     */
    public void setKnowledgeBase(){
        ArrayList<ClBeliefSet> bases = new ArrayList<>();

        /* Define signature */
        Proposition b = new Proposition("b"); //bird
        Proposition f = new Proposition("f"); //flying
        Proposition p = new Proposition("p"); //penguin
        Proposition w = new Proposition("w"); //winged animal

        Proposition a = new Proposition("a");
        Proposition c = new Proposition("c");
        Proposition d = new Proposition("d");
        Proposition e = new Proposition("e");
        Proposition h = new Proposition("h");
        Proposition s = new Proposition("s");
        Proposition k = new Proposition("k");
        Proposition l = new Proposition("l");
        Proposition t = new Proposition("t");

        /* Add Conditionals */
        penguin.add(new Conditional(b,f));
        penguin.add(new Conditional(p,b));
        penguin.add(new Conditional(p,new Negation(f)));
        penguin.add(new Conditional(b,w));

        penguin_z0.add(new Conditional(b,f));
        penguin_z0.add(new Conditional(b,w));

        penguin_z1.add(new Conditional(p,b));
        penguin_z1.add(new Conditional(p,new Negation(f)));

        penguin_c1.add(new Conditional(b,f));
        penguin_c1.add(new Conditional(p,b));
        penguin_c1.add(new Conditional(p,new Negation(f)));
        penguin_c2.add(new Conditional(b,w));

        thesis_c1.add(new Conditional(t,new Negation(f)));

        thesis_c2.add(new Conditional(s,t));
        thesis_c2.add(new Conditional(t,new Negation(e)));
        thesis_c2.add(new Conditional(s,e));

        thesis_c3.add(new Conditional(s,new Negation(k)));

        thesis.add(new Conditional(t,new Negation(f)));
        thesis.add(new Conditional(s,t));
        thesis.add(new Conditional(t,new Negation(e)));
        thesis.add(new Conditional(s,e));
        thesis.add(new Conditional(s,new Negation(k)));

        chainLonger_c1.add(new Conditional(f,a));
        chainLonger_c2.add(new Conditional(p,f));
        chainLonger_c2.add(new Conditional(new Negation(w),p));
        chainLonger_c3.add(new Conditional(t,new Negation(w)));

        chainLonger.add(new Conditional(f,a));
        chainLonger.add(new Conditional(p,f));
        chainLonger.add(new Conditional(new Negation(w),p));
        chainLonger.add(new Conditional(t,new Negation(w)));

        chain.add(new Conditional(p,f));
        chain.add(new Conditional(f,a));
        chain.add(new Conditional(a,p));

        circle.add(new Conditional(p,f));
        circle.add(new Conditional(f,a));
        circle.add(new Conditional(w,p));
        circle.add(new Conditional(a,w));

        starPre.add(new Conditional(p,new Negation(f)));
        starPre.add(new Conditional(p,new Negation(a)));
        starPre.add(new Conditional(p,w));

        starCon.add(new Conditional(f,w));
        starCon.add(new Conditional(p,w));
        starCon.add(new Conditional(a,w));

        carstart.add(new Conditional(s,a));
        carstart.add(new Conditional(new Negation(s),new Negation(a)));
        carstart.add(new Conditional(new Tautology(),new Negation(l)));
        carstart.add(new Conditional(new Tautology(),d));
        carstart.add(new Conditional(d,s));
        carstart.add(new Conditional(new Negation(d),new Negation(s)));
        carstart.add(new Conditional(new Negation(l),a));
        carstart.add(new Conditional(l,new Negation(a)));
        carstart.add(new Conditional(new Conjunction(new Negation(d),a),new Negation(s)));
        carstart.add(new Conditional(new Conjunction(new Negation(a),d),new Negation(s)));

    }


    public ClBeliefSet getPenguin() {
        return penguin;
    }

    public ClBeliefSet getPenguin_z0() {
        return penguin_z0;
    }

    public ClBeliefSet getPenguin_z1() {
        return penguin_z1;
    }

    public ClBeliefSet getPenguin_c1() {
        return penguin_c1;
    }

    public ClBeliefSet getPenguin_c2() {
        return penguin_c2;
    }


    public ClBeliefSet getThesis() {
        return thesis;
    }

    public ClBeliefSet getThesis_c1() {
        return thesis_c1;
    }

    public ClBeliefSet getThesis_c2() {
        return thesis_c2;
    }

    public ClBeliefSet getThesis_c3() {
        return thesis_c3;
    }

    public ClBeliefSet getChainLonger() {
        return chainLonger;
    }

    public ClBeliefSet getChainLonger_c1() {
        return chainLonger_c1;
    }

    public ClBeliefSet getChainLonger_c2() {
        return chainLonger_c2;
    }

    public ClBeliefSet getChainLonger_c3() {
        return chainLonger_c3;
    }

    public ClBeliefSet getChain() {
        return chain;
    }

    public ClBeliefSet getCircle() {
        return circle;
    }

    public ClBeliefSet getStarPre() {
        return starPre;
    }

    public ClBeliefSet getStarCon() {
        return starCon;
    }


}
