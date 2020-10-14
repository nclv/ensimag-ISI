/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */

/**
 *
 * @author viardots
 */
public class Constante extends ExpressionAbstraite{
    private double valeur;
    public Constante(double d) {
        valeur = d;
    }

    @Override
    public String toStringInfixe() {
        return "";
    }
    
}
