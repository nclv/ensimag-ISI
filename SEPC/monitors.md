See [Synchronizing Threads in Java](http://www.cs.sjsu.edu/faculty/pearce/modules/lectures/j2se/multithreading/synch1.htm).

---

process 1:
synchro1() {
    m.lock()
    cond.wait(m)
}

process 2: 
synchro1() {
    m.lock()
    cond.wait(m)
}

process 3: 
synchro1() {
    m.lock()
    cond.wait(m)
}

Seul P1 peut s'exécuter. P2 et P3 sont placés dans la file des mutex.
Ensuite le wait de P1 est exécuté.
P1 va être bloqué sur la file des processus bloqués par la condition. P2 est libéré de la file des mutex.
Ensuite le wait de P2 est exécuté.
P2 va être bloqué sur la file des processus bloqués par la condition. P3 est libéré de la file des mutex.
Ensuite le wait de P3 est exécuté.
P3 va être bloqué sur la file des processus bloqués par la condition. Il n'y a plus de processus dans la file des mutex.
Il y a inter-blocage. Les 3 processus attendent l'envoie d'un signal d'un autre processus.

On ajoute à la suite un 4ème processus qui appelle
synchro2() {
    m.lock()
    cond.signal()
    m.unlock()
}
Tous les processus sont libérés.

---

Q3. 

monitor
    mutex m
    condition c // bloqué si le nbprocessus < N && tour == montour.
    int nbprocessus = 0 
    int tour = 0; 
    // Solution qui répond au problème mais utilisable qu'une fois. -> Comment faire pour qu'il soit utilisable plusieurs fois? 
    // tour 
    barriere(){
        lock(&m)
        montour = tour
        nbprocessus++
        while ((nbprocessus < N) && (tour == montour)) {
            wait(&c, &m)
        }
        if ((nbprocessus == N) && (tour == montour)) {
            tour++
            nbprocessus = 0
            broadcast(&c)
        }
        unlock(&m)
    }

lecteur / rédacteur -> Correction 

mutex m 
condition cecr
condition clect
int nblect = 0
int nblect_att = 0
int nbecr = 0
int nbecr_att = 0


debut_lire()
    lock(&m)
    nblect_att++
    while ((nbecr == 1) || (nbecr_att > 0))
        wait(&clect,&m)
    broadcast(&clect)
    nblect_att--;
    nblect++
    unlock(&m)


fin_lire()
    lock(&m)
    nb_lect--
    if (nblect == 0) {
        signal(&cecr)
    }
    unlock(&m)


debut_ecr()
    lock(&m)
    nbecr_att++
    while (nbecr == 1 || nblect > 0)
        wait(&cecr,&m)
    nbecr_att--
    nbecr++
    unlock(&m)


fin_ecr()
    lock(&m)
    nb_ecr--
    if (nbecr_att > 0) 
        signal(&cecr)
    else if (nblect_att > 0)
        signal(&clect)
    unlock(&m)