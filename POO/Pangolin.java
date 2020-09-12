/**
 * Cette classe fournit l'implantation d'un Pangolin, petit mammifère d'Asie et
 * d'Afrique ressemblant « à un artichaut à l'envers avec des pattes, prolongé
 * d'une queue à la vue de laquelle on se prend à penser qu'en effet, le
 * ridicule ne tue plus. »
 *
 * @author Sylvain B.
 * @version 1.0
 */
public class Pangolin {
    /** la coordonnée x du pangolin. */
    private double x;
    /** la coordonnée y du pangolin. */
    private double y;
    /** le nom du pangolin (traditionnellement Gérard ou Toto). */
    private String name;
    /** le nombre d'écailles du pangolin (doit être strictement positif). */
    private int nbEcailles;
    // Un attribut de classe, partagé par tous les pangolins
    private static int nbPangolins = 0;

    public Pangolin(String nom, double xInit, double yInit, int nbEcailles) {
        nbPangolins++;
        this.name = nom;
        this.x = xInit;
        this.y = yInit;
        this.setNbEcailles(nbEcailles);
    }

    public Pangolin(String nom, int nbEcailles) {
        this(nom, 0, 0, nbEcailles); // Appel au constructeur à quatre paramètres
    }

    /**
     * Translate un pangolin.
     *
     * @param dx la coordonnée x de translation
     * @param dy la coordonnée y de translation
     */
    public void translater(double dx, double dy) {
        this.x += dx;
        this.y += dy;
    }

    /**
     * Cette méthode émet le cri caractéristique du pangolin et l'affiche sur la
     * sortie standard.
     */
    public void crier() {
        System.out.println("Gwwark Rhââgn Bwwikk"); // Cri du pangolin
    }

    public int getNbEcailles() {
        return this.nbEcailles;
    }

    // Une méthode de classe, indépendante de toute instance particulière
    public static int getNbPangolins() {
        return nbPangolins; // ou return Pangolin.nbPangolin ;
    }

    public void setNbEcailles(int nb) {
        if (nb <= 0) {
            throw new IllegalArgumentException("Le nombre d'écailles doit être strictement positif !");
        }
        this.nbEcailles = nb;
    }

    @Override
    public String toString() {
        return "Le Pangolin " + this.name + "(" + this.nbEcailles + " écailles)";
    }

    @Override
    public boolean equals(Object other) {
        if (other instanceof Pangolin) {
            return ((Pangolin) other).name.equals(this.name);
        }
        return false;
    }
}