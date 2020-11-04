package arithmetique;

public class TestEval {
	public static void main(String[] args) {
		// création de l'environnement
		Env env = new Env();
		env.associer("y", new Constante(2));
		env.associer("x", new Constante(1));
		env.associer("a", new Constante(9));
		env.associer("b", new Constante(3));
		System.out.println(env);

		ExpAbstraite exp;
		// teste l'expression préfixée * y 3
		exp = new BinaireMult(new Variable("y"), new Constante(3));
		System.out.println(exp.toStringInfixe());
		System.out.print("Valeur de l'expression, compte tenu des valeurs des variables : ");
		System.out.println(exp.evaluer(env));

		// teste l'expression préfixée * + x x 5
		exp = new BinaireMult(new BinairePlus(new Variable("x"), new Variable("x")), new Constante(5));
		System.out.println(exp.toStringInfixe());
		System.out.print("Valeur de l'expression, compte tenu des valeurs des variables : ");
		System.out.println(exp.evaluer(env));

		// teste l'expression préfixée * -3.5 sin + a b
		exp = new BinaireMult(new Constante(-3.5),
				new UnaireSin(new BinairePlus(new Variable("a"), new Variable("b"))));
		System.out.println(exp.toString());
		System.out.print("Valeur de l'expression, compte tenu des valeurs des variables : ");
		System.out.println(exp.evaluer(env));
	}
}
