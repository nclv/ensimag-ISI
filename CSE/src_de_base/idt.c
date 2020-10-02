/* 
    Interrupts are handled via the Interrupt Descriptor Table (IDT). 
    The IDT describes a handler for each interrupt. The interrupts are numbered (0 - 255) and the handler for 
    interrupt i is defined at the ith position in the table. There are three different kinds of handlers for 
    interrupts: Task handler, Interrupt handler, Trap handler

    The only difference between an interrupt handler and a trap handler is that the interrupt handler disables 
    interrupts, which means you cannot get an interrupt while at the same time handling an interrupt. 
*/

#include "inttypes.h"

#include "io.h"
#include "idt.h"

/* Nombre d'interruptions ou encore nombre d'entrée dans l'IDT */
#define NUM_IDT_ENTRIES (256)

idt_entry_t idt_entries[NUM_IDT_ENTRIES];

/*
    Initialisation de la table des vecteurs d’interruption

    On appelera simplement init_traitant_IT(32, traitant_IT_32); 
    pour initialiser la table des vecteurs d'interruption.

    Un traitant est un pointeur de fonction.
    "Instead of using bytes (or unsigned integers) use packed structures to make the code more readable." See idt.h.
*/
void init_traitant_IT(int32_t num_IT, void (*traitant)(void)) {

}

void tic_PIT(void) {
    pic_acknowledge();

    /* Affichage de l'horloge */
    // TODO
}