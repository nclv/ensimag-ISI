package arithmetique;

public class BinairePlus extends ExpBinaire{
    @Override
    public String toStringInfixe() {
        return "(" + this.getOpGauche().toStringInfixe() + " + " + this.getOpDroite().toStringInfixe() + ")";
    }

    @Override
    public double evaluer(Env env) {
        return this.getOpGauche().evaluer(env)
                + this.getOpDroite().evaluer(env);
    }

    public BinairePlus(ExpAbstraite opGauche, ExpAbstraite opDroite) {
        this.setOpGauche(opGauche);
        this.setOpDroite(opDroite);
    }
}
