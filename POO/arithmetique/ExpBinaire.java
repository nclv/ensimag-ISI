package arithmetique;

public abstract class ExpBinaire extends ExpAbstraite{
    private ExpAbstraite opGauche, opDroite;

    public ExpAbstraite getOpGauche() {
        return opGauche;
    }

    public void setOpGauche(ExpAbstraite opGauche) {
        this.opGauche = opGauche;
    }

    public ExpAbstraite getOpDroite() {
        return opDroite;
    }

    public void setOpDroite(ExpAbstraite opDroite) {
        this.opDroite = opDroite;
    }
}
