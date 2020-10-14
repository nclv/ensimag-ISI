package arithmetique;

public class UnaireCos extends ExpUnaire {
    @Override
    public String toStringInfixe() {
        return "cos(" + this.getOperande().toStringInfixe() + ")";
    }

    public UnaireCos(ExpAbstraite operande) {
        this.setOperande(operande);
    }
}
