# TP2.

Donner une adresse IP à chaque PC.

`ifconfig bge0 192.168.0.(10/20/30/40)`

Se connecter au switch.

`telnet 192.168.0.254`

Créer les vlans.

```bash
configure terminal
vlan 10
exit
vlan 20
exit
vlan 30
exit
vlan 40
exit
show vlans
```

Donner une IP au vlan et attribuer les ports.

```
vlan 10
ip address 192.168.10.254/24
untagged 1
untagged 2
vlan 20
ip address 192.168.20.254/24
untagged 3
tagged 2

vlan 30
ip address 192.168.30.254/24
untagged 4
tagged 3
vlan 40
ip address 192.168.40.254/24
show ru
```

Créer une interface `interfD` sur PC2.

`ifconfig vlan create vlan 20 vlandev bge0 name interfD`

On donne les bonnes IPs aux PC1 et PC2 sur le vlan 10 (en fait non, sur bge0. On a gardé seulement le vlan 20)

```bash
ifconfig bge0 192.168.10.1
ifconfig bge0 192.168.10.2
```

Sur PC1 et PC3 `routed -Pripv2 -Pno_rdisc -d -i -q`

Sur PC2 activer le routage

```bash
sysctl net.inet.ip.forwarding=1
routed -Pripv2 -Pno_rdisc -d -i -s
```

Sur les 3 ordinateurs `netstat -rnf inet`. On a bien le routage de PC1 vers PC3 (vérifié avec ping).

---

Capturer des paquets RIP sur PC2 `tcpdump -i bge# -v` et relancer `routed` sur PC1.

Destination multicast (224.0.0.9) pour request RIP à tous les voisins. UDP port 520.

Requête avec Metric 16. Réponse Metric 1 pour vlan 10 et vlan 20.

Période d'annonce par défaut de 30secs.

---

Afficher le contenu de la table des démons RIP `rtquery -n`

---

Simuler une déconnection réseau, lancer `netstat -rnf inet` et `rtquery -n` à intervalles réguliers. (attente de 3min)

La gateway pour la destination 192.168.20.0/24 est passée de 192.168.10.2 (bge0) à 129.88.241.140 (em0). Pas de changement de la table RIP. (attention, em0 n'est pas down)

Si em0 est down, passage de Metric à 16 pour 192.168.20.0/24. Ensuite disparition de l'entrée dans `rtquery -n`. L'entrée `192.168.20.0/24 192.168.10.2 UG bge0` disparait de la table de routage.
(on a les mêmes suppressions d'entrées pour 129.88.241.0/21).

Reconnection du réseau. (attente de 30sec)

Tout revient comme avant. Retour des entrées dans la table de routage et la table RIPv2.

---

`route flush`

Split-horizon : métrique maximale de 15, 16 si inaccessible. On ne recommunique pas ce qu'on a appris. Avec poison-reverse on a Metric 16.




