package arithmetique;

import java.util.*;

public class TestParser {

    public static void main(String[] args) {

        Scanner input = new Scanner(System.in);
        System.out.println(
                "Veuillez saisir l'expression en notation infixée. Utilisez des espaces entre chaque element ! : ");
        System.out.println(" Exemple :  + x * sin y 0.1 ");
        System.out.println("C'est à vous !");

        String exprString = input.nextLine();

        System.out.println("Vous avez saisi : " + exprString);
        Scanner sc = new Scanner(exprString);

        ExpAbstraite exp = parser(sc);
        if (sc.hasNext()) {
            // pas normal !
            throw new RuntimeException("Erreur. Expression mal formée");
        }

        System.out.println(exp.toString());

        while (true) {
            // création de l'environnement stockant les valeurs des variables
            System.out.println("-----------------------");
            System.out.println("Veuillez saisir les valeurs de toutes les variables (environnement)");
            System.out.println("  Format : <variable> <valeur> <variable> <valeur> sur une seule ligne.");
            System.out.println("  Exemple x 2.5 y 3.1416 .... ");
            System.out.println("Tapez exit pour sortir");
            System.out.println("C'est à vous !");
            input = new Scanner(System.in);
            String envString = input.nextLine();
            if (envString.equals("exit")) {
                System.out.println("Bye bye");
                System.exit(0);
            }
            sc = new Scanner(envString);
            try {
                Env env = parserEnvironnement(sc);
                System.out.println("Expression    : " + exp.toStringInfixe());
                System.out.println("Environnement : " + env);
                double resultat = exp.evaluer(env);
                System.out.print("Valeur de l'expression, compte tenu de l'environnement : ");
                System.out.println(resultat);
            } catch (Exception e) {
                System.out.println();
                System.out.println("erreur detectee : " + e);
                System.out.println("Recommencez !");
            }
        }

        // Env env = new Env();
        // env.associer("y", 2);
        // env.associer("x", 1);
        // env.associer("a", 9);
        // env.associer("b", 3);
        // System.out.print(
        // "Valeur de l'expression, compte tenu des valeurs des variables : ");
        // System.out.println( exp.evaluer(env) );
    }

    static ExpAbstraite parser(Scanner sc) {
        if (!sc.hasNext()) {
            throw new RuntimeException("parsing impossible : il manque des operandes !");
        }

        String op = sc.next();

        switch (op) {
            case "+":
                ExpAbstraite opGauche = parser(sc);
                ExpAbstraite opDroite = parser(sc);
                return new BinairePlus(opGauche, opDroite);

            case "*":
                return new BinaireMult(parser(sc), parser(sc));

            case "sin":
                return new UnaireSin(parser(sc));

            case "cos":
                return new UnaireCos(parser(sc));
        }

        try {
            double d = Double.parseDouble(op);
            return new Constante(d);
        } catch (NumberFormatException e) {
            // TODO: jamais laisser vide!
        }

        // est-ce une variable ?
        if (op.matches("[a-zA-Z]+?")) {
            // variable : uniquement des lettres !
            return new Variable(op);
        }

        throw new RuntimeException("parsing impossible : operateur '" + op + "' non reconnu");
    }

    static Env parserEnvironnement(Scanner sc) {
        Env env = new Env();

        while (sc.hasNext()) {
            String varStr = sc.next();
            // est-ce une variable ?
            if (varStr.matches("[a-zA-Z]+?")) {
                String dblStr = sc.next();
                double d = Double.parseDouble(dblStr);
                env.associer(varStr, d);
            } else {
                throw new RuntimeException("Erreur. Nom de variable attendu");
            }
        }
        return env;
    }
}
