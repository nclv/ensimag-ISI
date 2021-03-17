<%@ page contentType="text/html" pageEncoding="UTF-8"%>
<%@ page isErrorPage="true" %>
<!DOCTYPE html>
<html>
    <head>
        <meta charset="UTF-8">
        <title>Erreur !</title>
    </head>
    <body>
        <h1>Erreur</h1>
        <p>L’erreur suivante s’est produite :
            ${pageContext.errorData.throwable.message}
        </p>
        <p>Retour à la <a href="index.html">page d’accueil</a></p>
    </body>
</html>
