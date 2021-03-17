### Analyse en moyenne: calcul du minimum/maximum
[not a rigorous proof](https://stackoverflow.com/a/6735854)
[permutations](http://www.ens-lyon.fr/denif/data/algorithmique_enslyon/07-08-semestre1/td/td1_min_corrige.pdf)
[average-case analysis](https://www.nitt.edu/home/academics/departments/cse/faculty/kvi/Slides%20MaxFind%20algorithm%20analysis.pdf)
[min-max](https://cs.stackexchange.com/questions/89842/average-case-analysis-for-finding-max-and-min-value-on-an-array)


### Chaines de Markov

Une chaîne dont tous les états sont **récurrents** admet pour **loi stationnaire** la loi définie par $π(x_i) := 1 / m(x_i)$, où $m(x_i)$ est l’espérance du temps de retour à l’état $x_i$ (si l’on est parti de $x_i$).

Une chaîne de Markov est dite **irréductible** lorsque tous ses états communiquent, c’est-à-dire lorsque, pour toute paire d’états $(x_i, x_j)$ la probabilité d’aller de l’un à l’autre est strictement positive.  Un état dans lequel on reste à coup sur lorsqu’on y parvient s’appelle un **état absorbant**. *Une chaîne présentant un état absorbant ne peut pas être irréductible*.

Une chaîne de Markov **récurrente** admet toujours une *mesure invariante (non nulle)*, et celle-ci sera unique à un facteur près dès lors que la chaîne de Markov est **irréductible**.