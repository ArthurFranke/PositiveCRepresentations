import org.tweetyproject.logics.cl.syntax.Conditional;

public class ConditionalKappa {
    Conditional conditional;
    int kappaNeg;
    int kappaPos;
    int kappaDiff;

    public ConditionalKappa(Conditional c, int kNeg, int kPos){
        this.conditional = c;
        this.kappaNeg = kNeg;
        this.kappaPos = kPos;
        this.kappaDiff = kNeg - kPos;
    }

    public Conditional getConditional() {
        return this.conditional;
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
        return  "Conditional " + conditional +
                ": kappa_neg = " + kappaNeg +
                ", kappa_pos = " + kappaPos;
        }
}

