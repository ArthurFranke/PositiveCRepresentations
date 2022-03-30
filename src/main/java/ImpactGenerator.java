import java.util.ArrayList;

public class ImpactGenerator {

    private ArrayList<int[]> output = new ArrayList<>();
    private int length;
    private int maxValue;

    public ImpactGenerator(int deltaSize, int maxValue) {
        this.length = deltaSize;
        this.maxValue = maxValue;
    }

    public ArrayList<int[]> generateCombinations() {
        ArrayList<String> zeichenListe = new ArrayList<>();

        for(int i = 1; i <= maxValue; i++){
            zeichenListe.add(Integer.toString(i));
        }
        getCombination("", length, zeichenListe);
        return output;
    }

    private void getCombination(String currentString, int anzahl, ArrayList<String> zeichenliste){
        if (anzahl>0) {
            for(var i=0; i<zeichenliste.size(); i++){
                getCombination(currentString + "," +zeichenliste.get(i),anzahl-1,zeichenliste);
            }
        }
        else {
            currentString = currentString.replaceFirst(",","");
            String[] text = currentString.split(",");
            int[] values = new int[text.length];
            for(int i=0; i<text.length; i++) {
                values[i] = Integer.parseInt(text[i]);
            }
            output.add(values);
        }
    }
}


