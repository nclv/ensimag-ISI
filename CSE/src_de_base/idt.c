/*
    Interrupts are handled via the Interrupt Descriptor Table (IDT).
    The IDT describes a handler for each interrupt. The interrupts are numbered
   (0 - 255) and the handler for interrupt i is defined at the ith position in
   the table. There are three different kinds of handlers for interrupts: Task
   handler, Interrupt handler, Trap handler

    The only difference between an interrupt handler and a trap handler is that
   the interrupt handler disables interrupts, which means you cannot get an
   interrupt while at the same time handling an interrupt.
*/

#include "inttypes.h"
#include "string.h"
#include "stdio.h"
#include "stdbool.h"

#include "io.h"
#include "segment.h"
#include "console.h"
#include "idt.h"

/* Nombre d'interruptions ou encore nombre d'entrée dans l'IDT */
#define NUM_IDT_ENTRIES (256)

static idt_entry_t idt[NUM_IDT_ENTRIES];

/*
 * Initialisation de la table des vecteurs d’interruption
 *
 * On appelera simplement init_idt_entry(32, traitant_IT_32);
 * pour initialiser la table des vecteurs d'interruption.
 *
 * Un traitant est un pointeur de fonction.
 * "Instead of using bytes (or unsigned integers) use packed structures to make
 * the code more readable." See idt.h.
 */
static void init_idt_entry(int32_t interrupt_index,
                             interrupt_handler_t interrupt_handler) {
    idt_entry_t *interrupt = &idt[interrupt_index];
    uint32_t handler = (uint32_t)interrupt_handler;

    interrupt->base_lo = handler & 0xFFFF;
    interrupt->base_hi = (handler >> 16) & 0xFFFF;
    interrupt->segment_selector = KERNEL_CS; /* kernel code segment offset */
    interrupt->flags = 0x8E00; /* interrupt gate: used to transfer control of
                                    execution across segments */
}

/**
 * Initialisation de la table des vecteurs d'interruption
 * Appelée dans kernel_start()
 */
void init_idt(void) {
    /* Suppression de l'adresse mémoire des interrupt handlers dans la table */
    memset(idt, 0, sizeof *idt);

    /* Construction de la table */
    init_idt_entry(32, traitant_IT_32);  // 32, irq0
}

/**
 * Renvoie l'heure
 *
 * @pre global variable compteur is set
 * @return 
 */
void get_hour(char *hour, uint32_t seconds) {
    sprintf(hour, "%02u:%02u:%02u", (seconds / 3600), ((seconds / 60) % 60), (seconds % 60));
}

/**
 * Programmable Interval Timer
 */
void tic_PIT(void) {
    /* 
     * When the variable is declared inside the function, it has local scope only to that function. 
     * To reduce the scope of a variable as much as possible is always good practice.
    */
    pic_acknowledge();
    
    static uint32_t compteur = 0;
    char hour[32] = "00:00:00";  // on laisse le compilateur déterminer la taille

    /* Affichage de l'horloge */
    if (compteur % CLOCKFREQ == 0) {
        get_hour(hour, (compteur / CLOCKFREQ));
        console_write_hour(hour);
    }
    compteur++;
}

/** 
 * L’octet récupéré est un tableau de booléens tel que la valeur du bit N décrit l’état de l’IRQ N : 
 * 1 si l’IRQ est masquée, 0 si elle est autorisé. Il faut donc forcer la valeur du bit N à la valeur
 * souhaitée (sans toucher les valeurs des autres bits) et envoyer ce masque sur le port de données.
 */
void masque_IRQ(uint32_t num_IRQ, bool masque) {
	(masque) ? set_IRQ_mask(num_IRQ) : clear_IRQ_mask(num_IRQ);
}