import org.tweetyproject.logics.pl.syntax.*;

public class App {
    public static void main(String[] args) {
        PlFormula helloWorld = new Proposition("Hello World");
        System.out.println(helloWorld);
    }
}
