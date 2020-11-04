package arithmetique;

public class ExpressionEvaluable implements Evaluable {
    private ExpAbstraite expAbstraite;
    private Env env;

    @Override
    public double evaluer() {
        return this.expAbstraite.evaluer(this.env);
    }

    public ExpressionEvaluable(ExpAbstraite expAbstraite, Env env) {
        this.expAbstraite = expAbstraite;
        this.env = env;
    }

    @Override
    public String toString() {
        return "ExpressionEvaluable [env=" + env + ", expAbstraite=" + expAbstraite + "]";
    }

}
