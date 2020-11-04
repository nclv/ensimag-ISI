package arithmetique;

public class ExpressionEvaluable implements Evaluable {
    private ExpAbstraite expAbstraite;
    private Env env;

    @Override
    public double evaluer() {
        return this.expAbstraite.evaluer(this.env);
    }
}
