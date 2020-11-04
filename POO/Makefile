# Ce Makefile permet de compiler le test de l'ihm en ligne de commande.
# Alternative (recommandee?): utiliser un IDE (eclipse, netbeans, ...)
# Le but est ici d'illustrer les notions de "classpath", a vous de l'adapter
# a votre projet.
#
# Organisation:
#  1) Les sources (*.java) se trouvent dans le repertoire src
#     Les classes d'un package toto sont dans src/toto
#     Les classes du package par defaut sont dans src
#
#  2) Les bytecodes (*.class) se trouvent dans le repertoire bin
#     La hierarchie des sources (par package) est conservee.
#     L'archive bin/gui.jar contient les classes de l'interface graphique
#
# Compilation:
#  Options de javac:
#   -d : repertoire dans lequel sont places les .class compiles
#   -classpath : repertoire dans lequel sont cherches les .class deja compiles
#   -sourcepath : repertoire dans lequel sont cherches les .java (dependances)

all: testAffichageInfixe testEval testInterfaceEvaluable

testAffichageInfixe:
	javac -d bin arithmetique/TestAffichageInfixe.java
testEval:
	javac -d bin arithmetique/TestEval.java
testInterfaceEvaluable:
	javac -d bin arithmetique/TestInterfaceEvaluable.java

# Execution:
exeAffichageInfixe: 
	java -classpath bin arithmetique.TestAffichageInfixe
exeEval:
	java -classpath bin arithmetique.TestEval
exeInterfaceEvaluable:
	java -classpath bin arithmetique.TestInterfaceEvaluable

clean:
	rm -rf bin/*.class
