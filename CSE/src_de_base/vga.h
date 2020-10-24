#ifndef __VGA_H__
#define __VGA_H__

#include <inttypes.h>

/* Enumération des couleurs */
enum vga_color {
    VGA_COLOR_BLACK = 0,
    VGA_COLOR_BLUE = 1,
    VGA_COLOR_GREEN = 2,
    VGA_COLOR_CYAN = 3,
    VGA_COLOR_RED = 4,
    VGA_COLOR_MAGENTA = 5,
    VGA_COLOR_BROWN = 6,
    VGA_COLOR_LIGHT_GREY = 7,
    VGA_COLOR_DARK_GREY = 8,
    VGA_COLOR_LIGHT_BLUE = 9,
    VGA_COLOR_LIGHT_GREEN = 10,
    VGA_COLOR_LIGHT_CYAN = 11,
    VGA_COLOR_LIGHT_RED = 12,
    VGA_COLOR_LIGHT_MAGENTA = 13,
    VGA_COLOR_LIGHT_BROWN = 14,
    VGA_COLOR_WHITE = 15,
};

/**
 * Concatenation de la couleur du texte et de celle du fond
 * 
 * @param fg couleur du texte
 * @param bg couleur du fond
 * @return bg concaténé à fg 
 */
static inline uint8_t vga_color_byte(enum vga_color fg, enum vga_color bg) {
    return (uint8_t)(fg | bg << 4);
}

/**
 * Concatenation du caractère et de la couleur
 * 
 * @param uc caractère à afficher
 * @param color byte contenant la couleur du caractère et du fond
 * @return uc concaténé à color
 */
static inline uint16_t vga_case(unsigned char uc, uint8_t color) {
    return (uint16_t)(uc | color << 8);
}

#endif