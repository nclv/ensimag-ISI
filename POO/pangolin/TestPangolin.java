package pangolin;

// Le nom de la classe est à votre convenance.
// L'usage est d'appeler TestXXX une classe qui contient le programme principal
public class TestPangolin {
    public static void main(String[] args) {
        // Le tableau args, de taille args.length, contient les arguments du programme
        // Ici définissez les instructions de votre programme principal
        Pangolin gerard = new Pangolin("Gérard", 0, 0, 1452);
        Pangolin gerard2 = new Pangolin("Gérard", 0, 0, 1452);
        System.out.println(gerard == gerard2); // Écrit "false"
        gerard2 = gerard;
        System.out.println(gerard == gerard2); // Écrit "true"

        Pangolin gerard3 = new Pangolin("Gérard", 0, 0, 1452);
        // récupère le nb de pangolins crées jusque-là
        System.out.println(gerard3.getNbPangolins()); // Bon, ça marche... Affiche 1.

        // Mais on peut aussi accéder à un membre de classe directement avec le nom de
        // la classe.
        // Et c’est d'ailleurs ce qu'on fait en général avec les membres de classe !
        System.out.println(Pangolin.getNbPangolins()); // Affiche 1 aussi.
    }
}
