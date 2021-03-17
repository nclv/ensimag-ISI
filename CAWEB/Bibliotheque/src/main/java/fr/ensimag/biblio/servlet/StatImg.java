package fr.ensimag.biblio.servlet;

import java.io.IOException;
import java.io.OutputStream;
import javax.servlet.ServletException;
import javax.servlet.annotation.WebServlet;
import javax.servlet.http.HttpServlet;
import javax.servlet.http.HttpServletRequest;
import javax.servlet.http.HttpServletResponse;
import org.jfree.chart.ChartFactory;
import org.jfree.chart.ChartUtilities;
import org.jfree.chart.JFreeChart;
import org.jfree.data.general.DefaultPieDataset;

@WebServlet(name = "StatImg", urlPatterns = {"/stat_img"})
public class StatImg extends HttpServlet {

    protected void doGet(HttpServletRequest request, HttpServletResponse response)
            throws ServletException, IOException {

        /* Récupération des données de formulaire */
        int grenoble = Integer.parseInt(request.getParameter("GRE"));
        int smh = Integer.parseInt(request.getParameter("SMH"));
        int gieres = Integer.parseInt(request.getParameter("GIE"));
        int autres = Integer.parseInt(request.getParameter("OTH"));

        /* Création du graphique camembert */
        DefaultPieDataset dataset = new DefaultPieDataset();
        String title = "Répartition des abonnés";
        dataset.setValue("Grenoble", grenoble);
        dataset.setValue("Saint-Martin d’Hères", smh);
        dataset.setValue("Gières", gieres);
        dataset.setValue("autres", autres);

        JFreeChart chart
                = ChartFactory.createPieChart(title, dataset);

        /* Envoi de la réponse */
        response.setContentType("image/png");
        try (OutputStream out = response.getOutputStream()) {
            ChartUtilities.writeChartAsPNG(out, chart, 500, 300);
        }
    }
}
