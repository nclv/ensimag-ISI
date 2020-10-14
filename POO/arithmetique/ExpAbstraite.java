package arithmetique;

public abstract class ExpAbstraite {
    abstract String toStringInfixe();
    abstract double evaluer(Env env);

    @Override
    public String toString() {
        return toStringInfixe();
    }
}
