package arithmetique;

public class UnaireCos extends ExpUnaire {
    @Override
    public String toStringInfixe() {
        return "cos(" + this.getOperande().toStringInfixe() + ")";
    }

    @Override
    public double evaluer(Env env) {
        return Math.cos(this.getOperande().evaluer(env));
    }

    public UnaireCos(ExpAbstraite operande) {
        this.setOperande(operande);
    }
}
