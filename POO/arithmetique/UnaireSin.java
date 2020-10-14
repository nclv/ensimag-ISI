package arithmetique;

public class UnaireSin extends ExpUnaire {
    @Override
    public String toStringInfixe() {
        return "sin(" + this.getOperande().toStringInfixe() + ")";
    }

    public UnaireSin(ExpAbstraite operande) {
        this.setOperande(operande);
    }
}
