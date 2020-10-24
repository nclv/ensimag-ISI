See [Dekker-Peterson](http://www.philippevirouleau.fr/dekker-peterson) and the [code](https://gitlab.ensimag.fr/systemes/exemples/dekker)

On peut avoir 3 problèmes: pas d'exclusion mutuelle, de l'inter-bloquage ou famine.

# Q.1

`gcc -S -c increment.c` permet de produire le code assembleur.

```S
movq	%rsp, %rbp
.cfi_def_cfa_register 6
movl	$5, -4(%rbp)
addl	$1, -4(%rbp)
movl	$0, %eax
popq	%rbp
```

Disons que pour cet exemple deux processeurs souhaitent incrémenter une même variable `i`, le code pseudo-assembleur correspondant à l’instruction `i++` est le suivant :

```S
load r0, $i  # charge la valeur à l'adresse de i dans le registre 0
inc r0  # incrémente i
store $i, r0  # enregistre la valeur de r0 à l'adresse mémoire de i
```

# Q.2

On fait sur chaque machine la suite d'instruction suivante en parallèle:

```S
lw t1, 1
addi t1, t1, 1
sw t1, i
```

`t1` n'est pas le même pour chaque machine.
On a un problème si le processeur exécute `addi` (M1), `lw` (M2) puis `sw` (M1) par exemple.

Le problème se pose si les deux processeurs effectuent le load avant que l’un des deux n’ait fait le store : dans ce cas là les deux processeurs vont incrémenter la valeur originale de `i`, ce qui, au final, n’aura incrémenté `i` qu’une seule fois sur les deux attendues.

Ce problème a été résolu par Dekker en 1966, et Peterson a proposé une solution plus élégante en 1981.

# Q.3

Exclusion mutuelle: On doit préciser quelle ressource doit être protégée dans la section critique.

```
entree_SC(i)
i++
sortie_SC(i)
```

On va chercher à construire les entrées et sorties en sections critiques.

# Q.4

[good gotos](https://stackoverflow.com/questions/245742/examples-of-good-gotos-in-c-or-c/245761)

```C
condition:
    if (while_condition) {
        while_content();
        goto condition;
    }
```

```S
while:
    lw t1, while_condition
    beq t1, zero, fin_while
    while_content
    j while
fin_while:
```

# Q.5

On dispose de `bool SC_used()` et de `leave_SC()`.
On a un `test_and_write` (lire et changer la valeur en une même instruction) ie. `SC_used()` se fait de manière atomique. Sinon le code suivant ne fonctionne pas.

```
entree_SC()
    -- attente active
    while SC_used()
        wait

sortie_SC()
    leave_SC()
```

# Q.6

On a une attente active.

# Q.7

Utilisation d’un booléen d’occupation. Un processeur qui rentre dans la section critique va modifier un booléen nommé `occ` pour indiquer qu’il l’utilise.

```
bool occ = false;
entree_SC()
    while (occ) {
        wait
    }
    occ = true


sortie_SC()
    occ = false
```

# Q.8

Il est possible d'avoir deux processus ayant `occ = true` et donc pas d'exclusion mutuelle.

# Q.9-10

Chacun son tour. L'exclusion mutuelle est bien assurée. On peut avoir une famine car un des processus veut accéder à la section critique mais ne peut pas parce qu'il n'essait pas d'y accéder.

```
int tour;
entree_SC(x)
    while (tour != x)
        wait

sortie_SC(x)
    tour = !x
```

# Q.11-12

Annonce de sa volonté d’entrer en section critique. On a bien exclusion mutuelle, pas de famine, mais on a un deadlock.

```
bool occ[2] = { false, false };
entree_SC(x)
    occ[x] = true  -- on déclare notre intention d'accéder
    while (occ[!x])
        wait

sortie_SC(x)
    occ[x] = false
```

# Q.13-14

Annonce de sa volonté, avec renonce. Toujours problème de deadlock à cause de la synchronisation. En se désynchronisant avec l'allocation d'un temps d'attente aléatoire à chaque processus on n'a plus de deadlock (// Ethernet: tirage d'un temps aléatoire avant de réémettre).

```
bool occ[2] = { false, false };
entree_SC(x)
wait:
    occ[x] = true  -- on déclare notre intention d'accéder
    if (occ[!x])
        occ[x] = false  -- on renonce temporairement pour laisser à l'autre processus le temps de prendre la main
        goto wait

sortie_SC(x)
    occ[x] = false
```

# Q.15-16

Demande et renonce si ce n’est pas mon tour. Pas de famine ou de deadlock mais pas d'exclusion mutuelle. Si celui à qui ce n'est pas le tour demande à entrer en section critique il va pouvoir entrer. Si ensuite celui à qui c'est le tour veut entrer dans la section critique il entre sans vérification car c'est son tour.

```
bool occ[2] = { false, false };
int tour;
entree_SC(x)
wait:
    occ[x] = true  -- on déclare notre intention d'accéder
    if (occ[!x] && tour == !x)
        occ[x] = false  -- on renonce temporairement pour laisser à l'autre processus le temps de prendre la main
        goto wait

sortie_SC(x)
    tour = !x
    occ[x] = false
```

# Q.17

Dekker.

```
bool occ[2] = { false, false };
int tour;
entree_SC(me, other)
wait:
    occ[me] = true  -- on déclare notre intention d'accéder
    if (occ[other])
        if (tour == me)  -- c'est son tour
wait2:
            if (occ[other])  -- on attend que l'autre ait renoncé avant d'entrer
                goto wait2
        else
            occ[me] = false  -- on renonce à accéder
wait3:
            if (tour != me)  -- on attend son tour avant de redemander
                goto wait3
            goto wait

sortie_SC(me, other)
    tour = other
    occ[me] = false
```

# Q.18

Peterson.

```
bool occ[2] = { false, false };
int dernier;
entree_SC(x)
    occ[x] = true  -- on déclare notre intention d'accéder
    dernier = x
wait:
    if (occ[!x])
        if (dernier == x)
            goto wait

sortie_SC(x)
    occ[x] = false
```

# Q.19