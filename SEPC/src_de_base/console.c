#include "console.h"

#include <inttypes.h>
#include <stddef.h>
#include <stdio.h>
#include <string.h>

#include "cpu.h"
#include "vga.h"

static const size_t VGA_WIDTH = 80;
static const size_t VGA_HEIGHT = 25;
static volatile uint16_t *const VGA_MEMORY_START = (volatile uint16_t *)0xB8000;

static uint8_t terminal_color;
static volatile uint16_t *terminal_buffer;
static size_t terminal_lig;
static size_t terminal_col;

/**
 * Renvoie un pointeur sur la case mémoire correspondant aux coordonnées fournies.
 * 
 * @param lig ligne,
 * @param col colonne,
 * @return memory pointer
 */
// static inline volatile uint16_t *ptr_mem(uint32_t lig, uint32_t col) {
//     return (volatile uint16_t *)(VGA_MEMORY_START) + 2 * (lig * 80 + col);
// }

/**
 * Ecrit le caractère c aux coordonnées spécifiées
 * 
 * @pre terminal_buffer doit pointer sur VGA_MEMORY_START
 * 
 * @param lig ligne,
 * @param col colonne,
 * @param uc caractère à écrire sur la case correspondant à la ligne et à la colonne
 */
void ecrit_car(unsigned char uc, uint32_t lig, uint32_t col, uint8_t color) {
    const size_t index = lig * VGA_WIDTH + col;
    terminal_buffer[index] = vga_case(uc, color);
}

/** 
 * Effacement des caractères à l'écran
 * 
 * @pre terminal_buffer doit pointer sur VGA_MEMORY_START
 * 
 * Functional if your discard volatile keyword:
 * uint16_t *terminal_buffer = (uint16_t *)VGA_MEMORY_START;
 * memset(terminal_buffer, 0, VGA_WIDTH * VGA_HEIGHT * 2);
 */
void clear(void) {
    for (size_t lig = 0; lig < VGA_HEIGHT; lig++) {
        for (size_t col = 0; col < VGA_WIDTH; col++) {
            const size_t index = lig * VGA_WIDTH + col;
            terminal_buffer[index] = vga_case(' ', terminal_color);
        }
    }
}

/**
 * Initialise le terminal: couleur, pointeur d'entrée et clear
 * 
 */
void init_terminal(void) {
    terminal_lig = 0;
    terminal_col = 0;
    terminal_color = vga_color_byte(VGA_COLOR_LIGHT_GREY, VGA_COLOR_BLACK);
    terminal_buffer = VGA_MEMORY_START;
    clear();
}

/**
 * Place le curseur à la position donnée
 * 
 * @param lig ligne,
 * @param col colonne,
 */
void place_curseur(uint32_t lig, uint32_t col) {
    uint16_t pos = lig * VGA_WIDTH + col;

    const unsigned char COMMAND_PORT = (unsigned char)0x3D4;
    const unsigned char DATA_PORT = (unsigned char)0x3D5;

    // indique à la carte que l’on va envoyer la partie basse de la position du curseur
    outb(COMMAND_PORT, 0x0F);
    // envoie cette partie basse sur le port de données
    outb(DATA_PORT, (uint8_t)(pos & 0xFF));
    // signaler l'envoie de la partie haute
    outb(COMMAND_PORT, 0x0E);
    // envoyer la partie haute
    outb(DATA_PORT, (uint8_t)((pos >> 8) & 0xFF));
}

/**
 * Affiche le caractère à l'écran
 * 
 * @param c caractère à écrire,
 */
void traite_car(char c) {
    unsigned char uc = c;
    ecrit_car(uc, terminal_lig, terminal_col, terminal_color);
    if (++terminal_col == VGA_WIDTH) {
        terminal_col = 0;
        if (++terminal_lig == VGA_HEIGHT)
            terminal_lig = 0;
    }
    place_curseur(terminal_lig, terminal_col);
}

void terminal_write(const char *data, size_t size) {
    for (size_t i = 0; i < size; i++)
        traite_car(data[i]);
}

void terminal_writestring(const char *data) {
    terminal_write(data, strlen(data));
}

void defilement(void);

void console_putbytes(const char *s, int len);