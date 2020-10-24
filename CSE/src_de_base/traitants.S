    .text
# cette directive sert a rendre l'etiquette publique
    .globl traitant_IT_32
# debut du traitant 
traitant_IT_32:
# sauvegarde des registres importants
    pushl %eax
    pushl %edx
    pushl %ecx
# appel a la fonction C realisant le traitant
# Programmable Interval Timer
    call tic_PIT
# restauration des registres importants
    popl %ecx
    popl %edx
    popl %eax
# fin du traitant
    iret

