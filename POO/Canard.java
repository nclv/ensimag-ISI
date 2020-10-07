public class Canard extends Animal {

    private String couleurPlumes;

    public Canard(String nom, float poids, String couleurPlumes) {
        super(nom, poids);
        setCouleurPlumes(couleurPlumes);
    }

    public String getCouleurPlumes() {
        return couleurPlumes;
    }

    public void setCouleurPlumes(String couleurPlume) {
        this.couleurPlumes = couleurPlume;
    }

    public void crier() {
        super.crier();
        System.out
                .println("Ce canard de " + this.getPoids() + "kg aux belles plumes" + this.couleurPlumes + "cancane !");
    }
}
