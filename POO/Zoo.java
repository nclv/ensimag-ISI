import java.util.LinkedList;

class Zoo {
    private String nom;
    private LinkedList<Animal> animaux;

    public Zoo(String nom) {
        this.nom = nom;
        animaux = new LinkedList<Animal>();
    }

    public int getNbAnimaux() {
        return animaux.size();
    }

    public void ajouteAnimal(Animal animal) {
        animaux.add(animal);
    }

    public void crier() {
        System.out.println("*** 1, 2, 3 crions:");
        for (Animal a : animaux) {
            a.crier();
        }
    }

    @Override
    public String toString() {
        StringBuffer sb = new StringBuffer();
        sb.append("Le zoo " + nom + " contient " + getNbAnimaux() + " animaux:");
        sb.append(animaux.toString());
        return sb.toString();

        // alternative:
        // return "le zoo " + nom + "contient:" + animaux;
    }
}
