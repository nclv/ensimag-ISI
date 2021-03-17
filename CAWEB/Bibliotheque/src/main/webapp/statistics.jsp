<%@ page contentType="text/html; charset=UTF-8" %>
<%@ page errorPage="WEB-INF/erreur.jsp" %>
<%@ page import="javax.sql.DataSource" %>
<%@ page import="javax.annotation.Resource" %>
<%@ page import="fr.ensimag.biblio.dao.VillesDAO" %>
<%!

@Resource(name = "jdbc/bibliotheque")
private DataSource ds;
    
private String donneesFormulaire (int gre, int smh, int gie, int oth) {
    return "GRE=" + gre + "&SMH=" + smh + "&GIE=" + gie + "&OTH=" + oth;
}

private String descriptionTextuelle (int gre, int smh, int gie, int oth) {
    return "Grenoble : " + gre + ", Saint-Martin d’Hères : " + smh
            + ", Gières : " + gie + ", Autres : " + oth;
}

%>
<%
    int gre, smh, gie, oth;
    VillesDAO villes = new VillesDAO(ds);
    gre = villes.count("GRE");
    smh = villes.count("SMH");
    gie = villes.count("GIE");
    oth = villes.count("OTH");
%>
<!DOCTYPE html>
<html>
    <head>
        <meta charset="UTF-8">
        <link rel="stylesheet" type="text/css" href="styles.css" />
        <title>Statistiques</title>
    </head>
    <body>
        <h1>Statistiques sur les villes de résidence</h1>

        Répartition des villes de résidence des adhérents de la bibliothèque :
        <img src="stat_img?<%= donneesFormulaire(gre, smh, gie, oth) %>"
             alt="<%= descriptionTextuelle(gre, smh, gie, oth) %>"/>
        <p>Retour vers <a href="index.html">l’accueil</a></p>
    </body>
</html>
