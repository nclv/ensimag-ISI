enum Couleur {
    ROUGE(255, 0, 0), VERT(0, 255, 0), BLEU(0, 0, 255);

    private int rouge, vert, bleu;

    Couleur (int rouge, int vert, int bleu) {
    this.rouge = rouge;
    this.vert = vert;
    this.bleu = bleu;
    }

    public String getHtmlCode() {
    return "#" + String.format("%02x", this.rouge)
        + String.format("%02x", this.vert)
        + String.format("%02x", this.bleu);
    }
}