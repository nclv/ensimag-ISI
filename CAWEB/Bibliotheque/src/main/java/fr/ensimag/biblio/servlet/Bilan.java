package fr.ensimag.biblio.servlet;

import java.io.IOException;
import java.io.PrintWriter;
import javax.servlet.ServletException;
import javax.servlet.annotation.WebServlet;
import javax.servlet.http.*;

@WebServlet(name = "Bilan", urlPatterns = {"/bilan"})
public class Bilan extends HttpServlet {

    protected void doGet(HttpServletRequest request, HttpServletResponse response)
            throws ServletException, IOException {

        /* On vérifie dans la session que l’utilisateur est bien connecté */
        HttpSession sess = request.getSession(false);        
        if (sess != null) {
            String name = (String) sess.getAttribute("utilisateur");
            if (name != null) {

                /* L’utilisateur est bien connecté, on envoie la réponse */
                response.setContentType("text/html;charset=UTF-8");
                try (PrintWriter out = response.getWriter()) {
                    out.println("<!DOCTYPE html>");
                    out.println("<html>");
                    out.println("<head>");
                    out.println("<link rel='stylesheet' type='text/css' href='styles.css' />");
                    out.println("<title>Bilan des emprunts</title>");
                    out.println("</head>");            
                    out.println("<body>");
                    /* on sait que name n’est pas null */
                    out.println("Liste des emprunts de " + name);
                    out.println("<ul>");
                    out.println("<li><span>Les Travailleurs de la Mer</span>, Victor Hugo</li>");
                    out.println("<li><span>CSS 2 - Pratique du design web</span>, Raphaël Goetter</li>");
                    out.println("<li><span>The C++ Programming Language</span>, Bjarne Stroustrup</li>");
                    out.println("</ul>");
                    out.println("</body>");
                    out.println("</html>");
                }

                /* On a fini */
                return;
            }
        }
        /* Si la session n’existe pas ou ne contient pas "utilisateur", l’utilisateur n’est pas connecté */
        response.sendRedirect("login.html");
    }
}
