import org.tweetyproject.logics.cl.syntax.Conditional;

public class ConditionalKappa {
    Conditional c;
    int kappaNeg;
    int kappaPos;
    int kappaDiff;

    public ConditionalKappa(Conditional c, int kappaNeg, int kappaPos){
        this.c = c;
        this.kappaNeg = kappaNeg;
        this.kappaPos = kappaPos;
        this.kappaDiff = kappaNeg - kappaPos;
    }

    public Conditional getC() {
        return this.c;
    }

    public int getKappaNeg() {
        return this.kappaNeg;
    }

    public int getKappaPos() {
        return this.kappaPos;
    }

    public int getKappaDiff() {
        return this.kappaDiff;
    }

    @Override
    public String toString() {
        return  "Conditional " + c +
                ": kappa_neg = " + kappaNeg +
                ", kappa_pos = " + kappaPos + "\n";
        }
}

