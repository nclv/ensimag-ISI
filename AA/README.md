# Algorithmes probabilistes

Un algorithme probabiliste utilise une nouvelle opération bit_random() qui retourne avec probaibilté 0 ou 1 avec probabilité 1/2 .

Pour une même entrée x donnée, 2 exécutions d'un même algo probabiliste peuvent donner une sortie différente => une exécution d'un algo probabiliste peut délivrer une sortie "erronée".

Un algorithme probabiliste est une variable aléatoire.

---

Intérêt : il suffit de garantir la probabilité minimum que la sortie soit correcte.

Efficacité : on obtient ainsi des algorithmes plus efficaces que des algos déterministes.

Simplicité : grâce à l'aléatoire, on peut éliminer des cas pathologiques .

---

A la construction, bit_random est initialisé (graine ou "seed"). Chaque appel à bit_random() est une variable aléatoire iid. On peut utliser plusieurs générateurs aléatoires indépendants (en parallèle par exemple).

---

Trouver une pièce correcte dans un ensemble de N qui en contient p. N incorrect avec p < 25%. 

- Algo déterministe : coût en pire cas: p.N+1 = \Theta(N).
- Algo probabiliste : on choisit une pièce au hasard : si elle est correcte, on la retourne, sinon on retourne "échec". Pr(échec) = p.

Si on fait K exécutions indépendantes, Pr(échec) = p^K    (diminution exponentielle de la probabilité d'échec)

Si on boucle infiniment tant que l'on a un tirage "echec": nombre moyen de tirages = 1/(1-p) donc 4/3 si p=1/4 : le cout moyen est proche du meilleur cout de l'algorithme déterministe.

---

Accès aléatoires dans une table de multiplication qui contient des éléments incorrects pour donner un résultat correct avec une prob d'erreur bornée (cf slide).

---

Technique importante : **répéter l'exécution d'un l'algo probabiliste sur une même entrée x fixées permet de diminuer (exponentiellement) la probabilité d'erreur**.

- **Las Vegas** : Zero side error (retourne la bonne réponse ou echec): classe de complexité préfixée par Z
- **Atlantic City** : Both sided error : erruer toujours possible: classe de complexité préfixée par B
- **Monte Carlo** : One-Sided Error : erreur que du coté "OUI" : classe de complexité préfixée par R. Exemple: Miller Rabin:  algorithme Monte Carlo de test de composition (ie non-primalité)

---

Analyse des algorithmes probabilistes: dénombrement, bornes de Chernov, techniques d'analyse récursive (exemple arbre ET-OU), ...

# Links

- [Rust function signatures](https://hoverbear.org/blog/reading-rust-function-signatures/)
- [Itérateurs parallèles](http://wagnerf.pages.ensimag.fr/algoa/cm4/resume.html)
- [Filter/collect et préfixe](http://wagnerf.pages.ensimag.fr/algoa/cm5/resume.html)
