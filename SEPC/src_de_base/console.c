#include <console.h>
#include <cpu.h>
#include <inttypes.h>
#include <stddef.h>
#include <stdio.h>
#include <string.h>
#include <vga.h>


#define VGA_WIDTH (80)
#define VGA_HEIGHT (25)

/** Plutôt que de définir VGA_MEMORY_START dans un #define, on garde une constante
 * C'est nécessaire pour faire passer un pointeur.
 * Cela permet d'avoir un symbole dans la table du debugger.
 * On peut l'utiliser pour initialiser des variables statiques.
 * On a le contrôle du type.
 */
// static const size_t VGA_WIDTH = 80;
// static const size_t VGA_HEIGHT = 25;
static uint16_t *const VGA_MEMORY_START = (uint16_t *)0xB8000;

// TODO: Create a console struct
static uint8_t console_color;
static uint16_t *console_buffer;
static size_t console_lig;
static size_t console_col;

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
 * Ecrit le caractère aux coordonnées spécifiées
 * 
 * @pre console_buffer doit pointer sur VGA_MEMORY_START
 * 
 * @param lig ligne,
 * @param col colonne,
 * @param uc caractère à écrire sur la case correspondant à la ligne et à la colonne
 */
static void write_char(const unsigned char uc, uint32_t lig, uint32_t col, uint8_t color) {
    const size_t index = lig * VGA_WIDTH + col;
    console_buffer[index] = vga_case(uc, color);
}

/** 
 * Effacement des caractères sur la console.
 * 
 * @pre console_buffer doit pointer sur VGA_MEMORY_START
 * 
 * Functional if your discard volatile keyword:
 * console_buffer = VGA_MEMORY_START;
 * memset(console_buffer, 0, VGA_WIDTH * VGA_HEIGHT * 2);
 * 
 * Functional
 * for (size_t lig = 0; lig < VGA_HEIGHT; lig++) {
       for (size_t col = 0; col < VGA_WIDTH; col++) {
            write_char(' ', lig, col, console_color);
        }
    }
 */
void clear_console(void) {
    for (size_t lig = 0; lig < VGA_HEIGHT; lig++) {
        for (size_t col = 0; col < VGA_WIDTH; col++) {
            write_char(' ', lig, col, console_color);
        }
    }

    console_lig = 0;
    console_col = 0;
}

/**
 * Initialise la console: couleur, pointeur d'entrée et clear.
 * 
 */
void init_console(void) {
    console_color = vga_color_byte(VGA_COLOR_LIGHT_GREY, VGA_COLOR_BLACK);
    console_buffer = VGA_MEMORY_START;
    clear_console();
}

/**
 * Place le curseur à la position donnée.
 * 
 * @param lig ligne,
 * @param col colonne,
 */
static void place_curseur(uint32_t lig, uint32_t col) {
    uint16_t pos = lig * VGA_WIDTH + col;

    static const unsigned short COMMAND_PORT = 0x3D4;
    static const unsigned short DATA_PORT = 0x3D5;

    // indique à la carte que l’on va envoyer la partie basse de la position du curseur
    outb(0x0F, COMMAND_PORT);
    // envoie cette partie basse sur le port de données
    outb((uint8_t)(pos & 0xFF), DATA_PORT);
    // signaler l'envoie de la partie haute
    outb(0x0E, COMMAND_PORT);
    // envoyer la partie haute
    outb((uint8_t)((pos >> 8) & 0xFF), DATA_PORT);
}

/**
 * Fait défiler le texte sur la console.
 */
static void console_scroll(void) {
    memmove(console_buffer, console_buffer + 80 * 2, 80 * 25 * 2);
}

/**
 * Affiche le caractère sur la console.
 * 
 * @pre console_col, console_lig and console_color are set in a call to init_console()
 * 
 * @param c caractère à écrire,
 */
static void handle_char(char c) {
    const unsigned char uc = c;

    switch (uc) {
        case '\n':
            console_col = 0;
            console_lig++;
            break;
        case '\b':
            if (console_col != 0) console_col--;
            break;
        case '\t':
            console_col = (console_col + 8) / 8 * 8;
            if (console_col >= VGA_WIDTH) {
                ++console_lig;
                console_col = 0;
            }
            break;
        case '\f':
            clear_console();
            break;
        case '\r':
            console_col = 0;
            break;
        default:
            write_char(uc, console_lig, console_col, console_color);
            if (++console_col == VGA_WIDTH) {
                console_col = 0;
                if (++console_lig == VGA_HEIGHT) {
                    console_lig = 0;
                    console_scroll();
                }
            }
            break;
    }
    place_curseur(console_lig, console_col);
}

/**
 * Ecrit data sur l'écran.
 * 
 * @pre console_col, console_lig and console_color are set in a call to init_console()
 * 
 * @param c caractère à écrire,
 */
void console_putbytes(const char *data, int len) {
    for (int i = 0; i < len; i++)
        handle_char(data[i]);
}