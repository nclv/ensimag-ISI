package fr.ensimag.biblio.servlet;

import java.io.IOException;
import java.io.PrintWriter;
import javax.servlet.ServletException;
import javax.servlet.annotation.WebServlet;
import javax.servlet.http.*;

@WebServlet(name = "Logout", urlPatterns = {"/logout"})
public class Logout extends HttpServlet {
    
    protected void doGet(HttpServletRequest request, HttpServletResponse response)
            throws ServletException, IOException {

        /* Destruction de la session si elle existe */
        HttpSession sess = request.getSession(false); // ne crée pas de session si elle n’existe pas déjà
        if (sess != null) sess.invalidate();

        /* Envoi de la réponse */
        response.setContentType("text/html;charset=UTF-8");
        try (PrintWriter out = response.getWriter()) {
            out.println("<!DOCTYPE html>");
            out.println("<html>");
            out.println("<head>");
            out.println("<title>Logout</title>");            
            out.println("</head>");
            out.println("<body>");
            out.println("Vous avez bien été déconnecté.");
            out.println("</body>");
            out.println("</html>");
        }
    }
}
