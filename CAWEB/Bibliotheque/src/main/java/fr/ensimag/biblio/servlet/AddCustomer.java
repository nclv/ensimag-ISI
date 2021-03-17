package fr.ensimag.biblio.servlet;

import java.io.IOException;
import java.io.PrintWriter;
import java.sql.Connection;
import java.sql.PreparedStatement;
import java.sql.SQLException;
import javax.annotation.Resource;
import javax.servlet.ServletException;
import javax.servlet.annotation.WebServlet;
import javax.servlet.http.HttpServlet;
import javax.servlet.http.HttpServletRequest;
import javax.servlet.http.HttpServletResponse;
import javax.sql.DataSource;

@WebServlet(urlPatterns = {"/add_customer"})
public class AddCustomer extends HttpServlet {

    protected void doPost(HttpServletRequest request, HttpServletResponse response)
            throws ServletException, IOException {

        /* Récupération des données de formulaire */        
        request.setCharacterEncoding("UTF-8");
        String texte = traiteDonnees(request);

        /* Envoi de la réponse */
        response.setContentType("text/html;charset=UTF-8");
        envoieReponse(texte, response);        
    }
    
    private void envoieReponse(String texte, HttpServletResponse response)
            throws IOException {
         
        try (PrintWriter out = response.getWriter()) {
            out.println("<!DOCTYPE html>");
            out.println("<html>");
            out.println("<head>");
            out.println("<link rel='stylesheet' type='text/css' href='styles.css' />");
            out.println("<title>Résumé de l’inscription</title>");
            out.println("</head>");
            out.println("<body>");
            out.println("<p>");
            out.println(texte);
            out.println("</p>");
            out.println("Retour vers <a href='index.html'>l’accueil</a>");
            out.println("</body>");
            out.println("</html>");
        }
    }
    
    @Resource(name = "jdbc/bibliotheque")
    private DataSource ds;
    
    private String traiteDonnees(HttpServletRequest request) {

        /* Récupération des données */
        String login, pass, nom, prenom, sexe, code_ville;
        login = request.getParameter("login");
        pass = request.getParameter("mdp");
        nom = request.getParameter("nom");
        prenom = request.getParameter("prenom");
        sexe = request.getParameter("sexe");
        code_ville = request.getParameter("ville");
        /* "inscription" peut avoir plusieurs valeurs */
        String[] inscription = request.getParameterValues("inscription");
    
        /* Vérification des données */
        
        if (login == null || pass == null || nom == null || prenom == null
            || sexe == null || code_ville == null || inscription == null) {
            
            return "Erreur : tous les champs doivent être remplis.<br/>"
                 + "Retour au <a href='register.html'>formulaire</a>";

        }
        
        /* Traitement des données */
        
        String lieu, accord, type_inscr;
        
        switch (code_ville) {
            case "GRE":
                lieu = "à Grenoble";
                break;
            case "SMH":
                lieu = "à Saint-Martin d’Hères";
                break;
            case "GIE":
                lieu = "à Gières";
                break;
            default:
                lieu = "loin";
        }

        if (sexe.equals("masculin")) {
            accord = "";
        } else {
            accord = "e";
        }
        
        if (inscription.length > 1) {
            type_inscr = "à la bibliothèque et à la discothèque";
        } else {
            if (inscription[0].equals("bib")) {
                type_inscr = "à la bibliothèque";
            } else {
                type_inscr = "à la discothèque";
            }
        }
        
        /* Mise à jour de la base de données */
        
        try (Connection c = ds.getConnection()) {
            PreparedStatement ps =
                c.prepareStatement("INSERT INTO Users VALUES (?,?,?)");
            ps.setString(1, login);
            ps.setString(2, pass);
            ps.setString(3, code_ville);
            ps.executeUpdate();
        } catch (SQLException sqle) {
            return "Erreur d’insertion dans la base de données : "
                    + sqle.getMessage();
        }        
        
        String texte = "Bienvenue " + prenom + " " + nom
                + ". Vous habitez " + lieu + " et vous vous êtes inscrit"
                + accord + " " + type_inscr + ".";

        return texte;
    }
    
}