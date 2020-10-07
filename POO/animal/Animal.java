package animal;

public class Animal {
    private String nom;
    private float poids;

    public Animal(String nom, float poids) {
        setNom(nom);
        setPoids(poids);
    }

    public String getNom() {
        return nom;
    }

    public void setNom(String nom) {
        this.nom = nom;
    }

    public float getPoids() {
        return poids;
    }

    public void setPoids(float poids) {
        this.poids = poids;
    }

    public void crier() {
        System.out.println(this.nom + " crie ...");
    }

    @Override
    public String toString() {
        return "Animal [nom=" + nom + ", poids=" + poids + "]";
    }
}