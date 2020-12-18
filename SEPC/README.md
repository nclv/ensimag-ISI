See [ensimag-malloc](https://gitlab.ensimag.fr/vincentn/ensimag-malloc) and the [buddy system](https://broquedf.pages.ensimag.fr/sepcovid/allocateur/#lalgorithme-du-compagnon-buddy-system)

Dans le code du dossier _src/_, aucune gestion des erreurs n'est effectué sur les méthodes de création des threads, mutex et sémaphores.

---

Un processus est un programme en exécution.

---

Le système d'exploitation:
 - fournit des abstractions de la machine physique et de ses périphériques,
 - fournit des abstractions de haut-niveaux aux utilisateurs et programmeurs,
 - comme les fichiers, gère et contrôle les droits d'accès,
 - lit et écrit dans des variables ou des zones de la mémoire des processus,
 - est un ensemble de procédures exécutées par le processeur,
 - configure le processeur pour isoler les différents processus,

---

Si deux threads écrivent la même variable entière (4 octets, processeur x86-64) sans synchronisation avec deux valeurs différentes non nulle, le résultat sera une des deux écritures.

---

Un thread partage le même espace de mémoire avec tous les threads composant son processus.

---

```C
int nb=0;
   mtx_t m;
   cnd_t c1;
   cnd_t c2;
   
void A() {
    while (1) {
    mtx_lock( &m );
    while(nb%2 != 0)
        cnd_wait( &c1,&m);

    printf("A\n");
    nb ++;
    cnd_signal(c2);
    mtx_unlock( & m );
    }
}
   
void B() {
    while (1) {
    mtx_lock( &m );
    while((nb)%2 == 0)
        cnd_wait(& c2, &m);

    printf("B\n");
    nb++;
    cnd_signal(c1);
    mtx_unlock( &m );
    }
}
```

Après initialisation des variables, les deux fonctions précédentes sont exécutées simultanément par deux threads d'un même processus. Le terminal associé au processus affiche alternativement A et B, commençant par A.

Même programme que pour la question précédente. Que se passe-t-il si deux threads exécutent la fonction A, et un thread la fonction B ? Le terminal affiche alternativement A et B, commençant par A/

---

La même adresse virtuelle utilisée par deux processus différents:
 - est traduite par deux tables de pages différentes,
 - peut avoir la même traduction en adresse physique,
 - n'a pas toujours la même traduction en adresse physique,

---

La MMU (Memory Management Unit) est un matériel qui traduit les adresses virtuelles manipulées par le programme s'exécutant sur le processeur en adresse physique manipulée par la mémoire.

---

Une table des pages:
 - est cachée dans la TLB,
 - est une structure de donnée creuse stockant la partie haute d'adresses physiques,
 - est modifiée par la MMU,
 - est modifiée par le système d'exploitation,
 - est stockée dans la mémoire,
 - est une structure de donnée creuse indexée par la partie haute des adresses virtuelles,
 - décrit la traduction des adresses virtuelles d'un seul processus,
 - est lue par la MMU,

---

La TLB (Translation Lookaside Buffer) est le cache des valeurs de la table des pages dans le processeur.

---