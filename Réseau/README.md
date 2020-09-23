# VLAN

See [tagged/untagged/native](https://networkdirection.net/articles/network-theory/taggeduntaggedandnativevlans/)

Lorsque l'on définit les ports associés à chaque VLAN, il y a 3 modes: Untagged et Tagged et No.

 - Untagged : **Le port n'est associé qu'à un seul VLAN**. C'est à dire que tout équipement raccordé à ce port fera partie du VLAN.

 - Tagged : Signifie que les trames qui arrivent et sortent sur le port sont marquées par une en-tête 802.1q supplémentaire dans le champs Ethernet. **Un port peut être "tagged" sur plusieurs VLAN différents.**
L'avantage du mode Tagged est la possibilité d'avoir un serveur pouvant communiquer avec toutes les stations des VLANs sans que les VLANs ne puissent communiquer entre eux.

 - No : Aucune configuration dans le VLAN. 