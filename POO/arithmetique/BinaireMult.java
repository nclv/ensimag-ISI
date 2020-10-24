package arithmetique;

public class BinaireMult extends ExpBinaire {
    @Override
    public String toStringInfixe() {
        return "(" + this.getOpGauche().toStringInfixe() + " * " + this.getOpDroite().toStringInfixe() + ")";
    }

    @Override
    public double evaluer(Env env) {
        return this.getOpGauche().evaluer(env)
                * this.getOpDroite().evaluer(env);
    }

    public BinaireMult(ExpAbstraite opGauche, ExpAbstraite opDroite) {
        this.setOpGauche(opGauche);
        this.setOpDroite(opDroite);
    }
}
