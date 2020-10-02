#include "io.h"

#include "cpu.h"
#include "inttypes.h"

/* The I/O ports */
#define VGA_COMMAND_PORT (0x3D4)
#define VGA_DATA_PORT (0x3D5)
#define PIC1_PORT_A (0x20)

/* The I/O port commands */
#define VGA_HIGH_BYTE_COMMAND (0x0E)
#define VGA_LOW_BYTE_COMMAND (0x0F)
#define PIC_ACK_COMMAND (0x20)

/**
 * pic_acknowledge:
 * Acknowledges an interrupt from PIC 1.
 * Send the byte 0x20 to PIC 1 that raised the interrupt.
 */
void pic_acknowledge(void) { outb(PIC_ACK_COMMAND, PIC1_PORT_A); }

/**
 * Place le curseur à la position donnée.
 *
 * @param pos position à laquelle déplacer le curseur,
 */
void set_cursor(uint16_t pos) {
    // indique à la carte que l’on va envoyer la partie basse de la position du curseur
    outb(VGA_LOW_BYTE_COMMAND, VGA_COMMAND_PORT);
    // envoie cette partie basse sur le port de données
    outb((uint8_t)(pos & 0xFF), VGA_DATA_PORT);
    // signaler l'envoie de la partie haute
    outb(VGA_HIGH_BYTE_COMMAND, VGA_COMMAND_PORT);
    // envoyer la partie haute
    outb((uint8_t)((pos >> 8) & 0xFF), VGA_DATA_PORT);
}