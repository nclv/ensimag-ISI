package arithmetique;

public class Constante extends ExpAbstraite{
    private double valeur;

    @Override
    public String toStringInfixe() {
        return Double.toString(this.valeur);
    }

    public Constante(double valeur) {
        this.valeur = valeur;
    }
}
