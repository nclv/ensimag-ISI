package arithmetique;

import java.util.HashMap;
import java.util.Map;

public class Env {
    Map<String, Evaluable> map = new HashMap<String, Evaluable>();

    public void associer(String nom, Evaluable valeur) {
        this.map.put(nom, valeur);
    }

    public double obtenirValeur(String nom) {
        return this.map.get(nom).evaluer();
    }

    @Override
    public String toString() {
        return map.toString();
    }
}
