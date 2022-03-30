import org.tweetyproject.logics.cl.syntax.ClBeliefSet;
import org.tweetyproject.logics.cl.syntax.Conditional;
import org.tweetyproject.logics.pl.syntax.Conjunction;
import org.tweetyproject.logics.pl.syntax.Negation;
import org.tweetyproject.logics.pl.syntax.Proposition;
import org.tweetyproject.logics.pl.syntax.Tautology;

import java.util.ArrayList;

public class KnowledgeBases {

    public ClBeliefSet getPenguin() {
        return penguin;
    }

    ClBeliefSet penguin = new ClBeliefSet();
    ClBeliefSet carstart = new ClBeliefSet();
    ClBeliefSet chain = new ClBeliefSet();
    ClBeliefSet circle = new ClBeliefSet();
    ClBeliefSet starPre = new ClBeliefSet();
    ClBeliefSet starCon = new ClBeliefSet();

    ClBeliefSet penguin_z0 = new ClBeliefSet();
    ClBeliefSet penguin_z1 = new ClBeliefSet();

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
        Proposition k = new Proposition("k"); //kiwi

        Proposition a = new Proposition("a"); //awesome kiwi
        Proposition c = new Proposition("c"); //crocodile
        Proposition d = new Proposition("d"); //descend from dinosaurs

        Proposition e = new Proposition("e"); //lays eggs
        Proposition h = new Proposition("h"); //huge animal
        Proposition s = new Proposition("s"); //super-penguin

        Proposition v = new Proposition("v");
        Proposition z = new Proposition("z");

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


        ClBeliefSet kb_lorenzo = new ClBeliefSet();
        kb_lorenzo.add(new Conditional(t,new Negation(f)));
        kb_lorenzo.add(new Conditional(s,t));
        kb_lorenzo.add(new Conditional(t,new Negation(e)));
        kb_lorenzo.add(new Conditional(s,new Negation(k)));
        kb_lorenzo.add(new Conditional(s,e));

        ClBeliefSet cars1 = new ClBeliefSet();
        cars1.add(new Conditional(new Tautology(),new Negation(h)));
        cars1.add(new Conditional(new Negation(h),b));
        cars1.add(new Conditional(h,new Negation(b)));

        ClBeliefSet cars2 = new ClBeliefSet();
        cars2.add(new Conditional(b,s));
        cars2.add(new Conditional(new Negation(b),new Negation(s)));
        cars2.add(new Conditional(new Tautology(),f));
        cars2.add(new Conditional(f,s));
        cars2.add(new Conditional(new Negation(f),new Negation(s)));
        cars2.add(new Conditional(new Conjunction(new Negation(f),b),new Negation(s)));
        cars2.add(new Conditional(new Conjunction(new Negation(b),f),new Negation(s)));

        ClBeliefSet cars = new ClBeliefSet(cars2);
        cars.add(new Conditional(new Tautology(),new Negation(h)));
        cars.add(new Conditional(new Negation(h),b));
        cars.add(new Conditional(h,new Negation(b)));

        ClBeliefSet cars3 = new ClBeliefSet();
        cars3.add(new Conditional(b,s));
        cars3.add(new Conditional(new Tautology(),new Negation(h)));
        cars3.add(new Conditional(new Tautology(),f));
        cars3.add(new Conditional(f,s));
        cars3.add(new Conditional(new Negation(h),b));

        ClBeliefSet cars4 = new ClBeliefSet();
        cars4.add(new Conditional(new Negation(b),new Negation(s)));
        cars4.add(new Conditional(new Negation(f),new Negation(s)));
        cars4.add(new Conditional(new Conjunction(new Negation(f),b),new Negation(s)));
        cars4.add(new Conditional(new Conjunction(new Negation(b),f),new Negation(s)));
        cars4.add(new Conditional(h,new Negation(b)));

        ClBeliefSet thesis = new ClBeliefSet();
        thesis.add(new Conditional(t,new Negation(f)));
        thesis.add(new Conditional(s,t));
        thesis.add(new Conditional(t,new Negation(e)));
        thesis.add(new Conditional(s,new Negation(k)));
        thesis.add(new Conditional(s,e));

        ClBeliefSet thesis_c1 = new ClBeliefSet();
        ClBeliefSet thesis_c2 = new ClBeliefSet();
        ClBeliefSet thesis_c3 = new ClBeliefSet();
        thesis_c1.add(new Conditional(t,new Negation(f)));
        thesis_c2.add(new Conditional(s,t));
        thesis_c2.add(new Conditional(t,new Negation(e)));
        thesis_c2.add(new Conditional(s,e));
        thesis_c3.add(new Conditional(s,new Negation(k)));

        ClBeliefSet thesis_kette = new ClBeliefSet();
        thesis_kette.add(new Conditional(p,f));
        thesis_kette.add(new Conditional(f,a));
        thesis_kette.add(new Conditional(a,w));

        ClBeliefSet thesis_kreis = new ClBeliefSet(thesis_kette);
        thesis_kreis.add(new Conditional(w,p));

        ClBeliefSet thesis_stern1 = new ClBeliefSet();
        thesis_stern1.add(new Conditional(p,new Negation(f)));
        thesis_stern1.add(new Conditional(p,new Negation(a)));
        thesis_stern1.add(new Conditional(p,w));

        ClBeliefSet thesis_stern2 = new ClBeliefSet();
        thesis_stern2.add(new Conditional(f,w));
        thesis_stern2.add(new Conditional(p,w));
        thesis_stern2.add(new Conditional(a,w));


        ClBeliefSet kb_lorenzo1 = new ClBeliefSet();
        kb_lorenzo1.add(new Conditional(t,new Negation(f)));
        kb_lorenzo1.add(new Conditional(t,new Negation(e)));

        ClBeliefSet kb_lorenzo2 = new ClBeliefSet();
        kb_lorenzo2.add(new Conditional(s,t));
        kb_lorenzo2.add(new Conditional(s,new Negation(k)));
        kb_lorenzo2.add(new Conditional(s,e));


        bases.add(kb_lorenzo); // 5
        bases.add(cars1);
        bases.add(cars2);
        bases.add(cars); // 8
        bases.add(thesis);    // 9
        bases.add(thesis_c1); //10
        bases.add(thesis_c2); //11
        bases.add(thesis_c3); //12
        bases.add(thesis_kette); // 13
        bases.add(thesis_kreis); // 14
        bases.add(thesis_stern1); // 15
        bases.add(thesis_stern2); // 16


        bases.add(kb_lorenzo1); // 19
        bases.add(kb_lorenzo2); // 20

    }
}
