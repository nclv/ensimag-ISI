public class Vache extends Animal {

    private int nombreTaches;

    public Vache(String nom, float poids, int nombreTaches) {
        super(nom, poids);
        setnombreTaches(nombreTaches);
    }

    public int getnombreTaches() {
        return nombreTaches;
    }

    public void setnombreTaches(int nombreTaches) {
        this.nombreTaches = nombreTaches;
    }

    public void crier() {
        // super.crier();
        System.out.println("Matthieu, la vache à " + this.nombreTaches + "taches qui tachent, crie... il meugle");
    }

}