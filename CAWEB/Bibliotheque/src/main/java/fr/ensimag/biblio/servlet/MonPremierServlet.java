package fr.ensimag.biblio.servlet;

import java.io.IOException;
import java.io.PrintWriter;
import javax.servlet.ServletException;
import javax.servlet.annotation.WebServlet;
import javax.servlet.http.HttpServlet;
import javax.servlet.http.HttpServletRequest;
import javax.servlet.http.HttpServletResponse;

@WebServlet(name = "MonPremierServlet", urlPatterns = {"/first"})
public class MonPremierServlet extends HttpServlet {

    protected void doPost(HttpServletRequest request, HttpServletResponse response)
            throws ServletException, IOException {

        /* Récupération des données de formulaire */
        request.setCharacterEncoding("UTF-8");
        String texte = request.getParameter("letexte");
        System.out.println(
            "données de formulaire récupérées (paramètre \"texte\") :" + texte
        );

        /* Envoi de la réponse */
        response.setContentType("text/html;charset=UTF-8");
        try (PrintWriter out = response.getWriter()) {
            out.println("<!DOCTYPE html>");
            out.println("<html>");
            out.println("<head>");
            out.println("<title>Servlet MonPremierServlet</title>");
            out.println("</head>");
            out.println("<body>");
            out.println("<p>Vous avez entré : " + texte + "</p>");
            out.println("</body>");
            out.println("</html>");
        }
    }
}
