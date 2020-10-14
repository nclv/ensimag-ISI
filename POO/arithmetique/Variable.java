package arithmetique;

public class Variable extends ExpAbstraite{
    private String nom;

    @Override
    public String toStringInfixe() {
        return this.nom;
    }

    public Variable(String nom) {
        this.nom = nom;
    }
}
