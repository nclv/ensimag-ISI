#include "console.h"

#include <inttypes.h>
#include <stddef.h>
#include <string.h>

#define ECRAN_BASE (0xB8000)
#define WIDTH (80)
#define HEIGHT (25)
// renvoie un pointeur sur la case mémoire correspondant aux coordonnées fournies
#define ptr_mem(lig, col) ((volatile uint16_t *)(ECRAN_BASE) + 2 * (lig * 80 + col))

/**
 * Ecrit le caractère c aux coordonnées spécifiées
 * 
 * @param lig ligne,
 * @param col colonne,
 * @param c caractère à écrire sur la case correspondant à la ligne et à la colonne
 * @param caractcolor couleur du caractère
 * @param backcolor couleur du fond
 */
void ecrit_car(uint32_t lig, uint32_t col, char c,
               unsigned char caractcolor, unsigned char backcolor) {
    uint16_t format = (backcolor << 4) | (caractcolor & 0x0F);
    volatile uint16_t *where = ptr_mem(lig, col);
    *where = c | (format << 8);
}

/** 
 * Parcours des lignes et des colonnes de l'écran pour écrire dans chaque case un espace
 * en blanc sur fond noir (afin d'initialiser les formats dans la mémoire)
 * memset a certains avantages (voir https://stackoverflow.com/questions/8528590/what-is-the-advantage-of-using-memset-in-c)
 */
void efface_ecran(void) {
    uint16_t *where = (uint16_t *)ECRAN_BASE;
    memset(where, 0, 80 * 25 * 2);
}

/**
 * Place le curseur à la position donnée
 * @param lig ligne,
 * @param col colonne,
 */ 
void place_curseur(uint32_t lig, uint32_t col) {
    uint16_t pos = lig * WIDTH + col;
 
    // indique à la carte que l’on va envoyer la partie basse de la position du curseur
	outb(0x3D4, 0x0F);
    // envoie cette partie basse sur le port de données
	outb(0x3D5, (uint8_t) (pos & 0xFF));
    // signaler l'envoie de la partie haute
	outb(0x3D4, 0x0E);
    // envoyer la partie haute
	outb(0x3D5, (uint8_t) ((pos >> 8) & 0xFF));
}
void traite_car(char c);
void defilement(void);

void console_putbytes(const char *s, int len);