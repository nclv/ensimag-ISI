#include "console.h"

#include "cpu.h"
#include "inttypes.h"
#include "io.h"
#include "stddef.h"
#include "stdio.h"
#include "string.h"
#include "vga.h"

#define VGA_WIDTH (80)
#define VGA_HEIGHT (25)

#define HOUR_LEN (8)

/** Plutôt que de définir VGA_MEMORY_START dans un #define, on garde une constante
 * C'est nécessaire pour faire passer un pointeur.
 * Cela permet d'avoir un symbole dans la table du debugger.
 * On peut l'utiliser pour initialiser des variables statiques.
 * On a le contrôle du type.
 */
// static const size_t VGA_WIDTH = 80;
// static const size_t VGA_HEIGHT = 25;
static volatile uint16_t *const VGA_MEMORY_START = (uint16_t *)0x000B8000;

// TODO: Create a console struct
static uint8_t console_color;
static uint8_t default_console_color;
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
 * memset(console_buffer, 0, VGA_WIDTH * VGA_HEIGHT * sizeof *uint16_t);
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
    default_console_color = console_color;
    console_buffer = (uint16_t *)VGA_MEMORY_START;
    clear_console();
}

/**
 * Place le curseur à la position donnée.
 * 
 * @param lig ligne,
 * @param col colonne,
 *
 * @pre set_cursor function from io.h
 */
static void place_curseur(uint32_t lig, uint32_t col) {
    uint16_t pos = (uint16_t)(lig * VGA_WIDTH + col);
    set_cursor(pos);
}

/**
 * Fait défiler le texte sur la console.
 * 
 * @pre console_lig = 24 and console_col = 0
 */
static void console_scroll(void) {
    /** 
     * Use with console_lig = 24 in handle_char()
     * Append text at the bottom
     */
    memmove(console_buffer, console_buffer + VGA_WIDTH,
            (VGA_WIDTH - 1) * VGA_HEIGHT * sizeof *console_buffer);
    // Or with a loop
    // for (int i = 0; i < VGA_HEIGHT; i++) {
    //     for (int m = 0; m < VGA_WIDTH; m++) {
    //         console_buffer[i * VGA_WIDTH + m] = console_buffer[(i + 1) * VGA_WIDTH + m];
    //     }
    // }
}

/**
 * Placer les coordonnées du curseur sur une nouvelle ligne.
 * Défilement du texte si besoin.
 */
static void new_line(void) {
    console_col = 0;
    if (++console_lig == VGA_HEIGHT) {
        console_lig = 24;
        console_scroll();
    }
}

/**
 * Affiche le caractère sur la console.
 * 
 * @pre console_col, console_lig, console_color and default_console_color are set in a call to init_console()
 * 
 * @param c caractère à écrire,
 */
static void handle_char(char c) {
    const unsigned char uc = (unsigned char)c;

    switch (uc) {
        case '\n':
            console_color = default_console_color;
            for (size_t col = console_col; col < VGA_WIDTH; col++) {
                write_char(' ', console_lig, col, console_color);
            }
            new_line();
            break;
        case '\b':
            if (console_col != 0) console_col--;
            break;
        case '\t': {
            console_color = default_console_color;
            size_t next_tab_col = (console_col + 8) / 8 * 8;
            for (size_t col = console_col; col < next_tab_col; col++) {
                write_char(' ', console_lig, col, console_color);
            }
            console_col = next_tab_col;
            if (console_col >= VGA_WIDTH) {
                new_line();
            }
            break;
        }
        case '\f':
            clear_console();
            break;
        case '\r':
            console_col = 0;
            break;
        default:
            write_char(uc, console_lig, console_col, console_color);
            if (++console_col == VGA_WIDTH) {
                new_line();
            }
            break;
    }

    place_curseur(console_lig, console_col);
}

/**
 * Ecrit data sur l'écran.
 * 
 * @pre console_col, console_lig, console_color and default_console_color are set in a call to init_console()
 * 
 * @param data chaîne de caractères à écrire,
 * @param len longueur de la chaîne de caractères,
 */
void console_putbytes(const char *data, int len) {
    for (int i = 0; i < len; i++)
        handle_char(data[i]);
}

/**
 * Ecrit data sur l'écran.
 * 
 * @pre console_col, console_lig, console_color and default_console_color are set in a call to init_console()
 * 
 * @param data chaîne de caractères à écrire,
 */
void console_write(const char *data) {
    size_t i = 0;
    while (data[i] != '\0') {
        handle_char(data[i]);
        i++;
    }
}

/**
 * Ecrit data en couleur sur l'écran.
 * 
 * @pre console_col, console_lig, console_color and default_console_color are set in a call to init_console()
 * 
 * @param data chaîne de caractères à écrire,
 * @param color_type 0:Success:GREEN, ...
 */
void console_write_color(const char *data, int color_type) {
    uint8_t color;
    switch (color_type) {
        case 0:
            color = vga_color_byte(VGA_COLOR_GREEN, VGA_COLOR_BLACK);
            break;
        default:
            color = vga_color_byte(VGA_COLOR_LIGHT_GREY, VGA_COLOR_BLACK);
            break;
    }

    console_color = color;
    console_write(data);
    console_color = default_console_color;
}

/**
 * Ecrit l'heure sur la console en haut à droite
 *
 * @param hour heure au format hh:mm:ss
 */
void console_write_hour(const char hour[HOUR_LEN]) {
    size_t i = 0;
    uint8_t col = VGA_WIDTH - HOUR_LEN;
    while (hour[i] != '\0') {
        write_char(hour[i], 0, col + i, console_color);
        place_curseur(0, col + i + 1);
        i++;
    }
    place_curseur(console_lig, console_col);
}