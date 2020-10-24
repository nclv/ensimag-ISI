package arithmetique;

public class Constante extends ExpAbstraite{
    private double valeur;

    @Override
    public String toStringInfixe() {
        return Double.toString(this.valeur);
    }

    @Override
    public double evaluer(Env env) {
        return this.valeur;
    }

    public Constante(double valeur) {
        this.valeur = valeur;
    }
}
