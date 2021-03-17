package fr.ensimag.biblio.servlet;

import java.io.IOException;
import java.io.PrintWriter;
import java.sql.*;
import javax.annotation.Resource;
import javax.servlet.ServletException;
import javax.servlet.annotation.WebServlet;
import javax.servlet.http.*;
import javax.sql.DataSource;

@WebServlet(name = "CheckUser", urlPatterns = {"/checkuser"})
public class CheckUser extends HttpServlet {
    
    @Resource(name = "jdbc/bibliotheque")
    private DataSource ds;
    
    private boolean isLoginValid(String login, String pwd)  throws SQLException {
        
        try (Connection c = ds.getConnection()) {
            /* Un PreparedStatement évite les injections SQL */
            PreparedStatement s = c.prepareStatement(
                "SELECT login FROM users WHERE login = ? AND password = ?"
            );
            s.setString(1, login);
            s.setString(2, pwd);
            ResultSet r = s.executeQuery();
            /* r.next() renvoie vrai si et seulement si la réponse contient au moins 1 ligne */
            return r.next();
        }

        /* Remarque : ici le bloc "try" a l’effet suivant :
         * 1) r.next() est évalué
         * 2) c.close() est appelé (car on va sortir du bloc "try" par l’instruction return)
         * 3) la méthode renvoie la valeur de r.next() évaluée précédemment
         */
    }
    
    protected void doPost(HttpServletRequest request, HttpServletResponse response)
            throws ServletException, IOException {

        /* Récupération des données de formulaire */
        request.setCharacterEncoding("UTF-8");
        String login = request.getParameter("login");
        String pass = request.getParameter("password");

        /* Vérification et traitement des données */
        String msg;
        try {
            if (login != null && pass != null && isLoginValid(login, pass)) {
                HttpSession session = request.getSession();
                session.setAttribute("utilisateur", login);
                msg = "Login correct";
            } else {
                msg = "Login incorrect";
            }
        } catch (SQLException e) {
            msg = "Erreur : la vérification de votre identifiant a échoué";
            e.printStackTrace(); // loggue l’erreur (de façon primitive)
        }

        /* Envoi de la réponse */
        response.setContentType("text/html;charset=UTF-8");
        try (PrintWriter out = response.getWriter()) {
            out.println("<!DOCTYPE html>");
            out.println("<html>");
            out.println("<head>");
            out.println("<meta charset=\"UTF-8\" />");
            out.println("<title>" + msg + "</title>");            
            out.println("</head>");
            out.println("<body>");
            out.println(msg + ". Retour à l’<a href=\"index.html\">accueil</a>");
            out.println("</body>");
            out.println("</html>");
        }
    }
}
