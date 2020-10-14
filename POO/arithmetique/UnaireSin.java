package arithmetique;

public class UnaireSin extends ExpUnaire {
    @Override
    public String toStringInfixe() {
        return "sin(" + this.getOperande().toStringInfixe() + ")";
    }

    @Override
    public double evaluer(Env env) {
        return Math.sin(this.getOperande().evaluer(env));
    }

    public UnaireSin(ExpAbstraite operande) {
        this.setOperande(operande);
    }
}
