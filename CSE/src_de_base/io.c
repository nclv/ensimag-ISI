#include "io.h"

#include "cpu.h"
#include "inttypes.h"

/* The I/O ports */
#define VGA_COMMAND_PORT (0x3D4)
#define VGA_DATA_PORT (0x3D5)
#define PIC1_COMMAND_PORT (0x20)
#define PIC1_DATA_PORT (0x21)
// See https://wiki.osdev.org/Programmable_Interval_Timer
#define PIT_CHANNEL_0_DATA_PORT (0x40)   // (read/write)
#define PIT_MODECOMMAND_REGISTER (0x43)  // (write only, a read is ignored)

/* The I/O port commands */
#define VGA_HIGH_BYTE_COMMAND (0x0E)
#define VGA_LOW_BYTE_COMMAND (0x0F)
#define PIC_ACK_COMMAND (0x20)
#define PIT_ONE_SHOT_MODE (0x34)

/**
 * pic_acknowledge:
 * Acknowledges an interrupt from PIC 1 (master PIC).
 * Send the byte 0x20 to PIC 1 that raised the interrupt.
 */
inline void pic_acknowledge(void) { outb(PIC_ACK_COMMAND, PIC1_COMMAND_PORT); }

/**
 * Place le curseur à la position donnée.
 *
 * @param pos position à laquelle déplacer le curseur,
 */
inline void set_cursor(uint16_t pos) {
    // indique à la carte que l’on va envoyer la partie basse de la position du curseur
    outb(VGA_LOW_BYTE_COMMAND, VGA_COMMAND_PORT);
    // envoie cette partie basse sur le port de données
    outb((uint8_t)(pos & 0xFF), VGA_DATA_PORT);
    // signaler l'envoie de la partie haute
    outb(VGA_HIGH_BYTE_COMMAND, VGA_COMMAND_PORT);
    // envoyer la partie haute
    outb((uint8_t)((pos >> 8) & 0xFF), VGA_DATA_PORT);
}

inline void set_IRQ_mask(uint32_t num_IRQ) {
    unsigned char value = inb(PIC1_DATA_PORT) | (1 << num_IRQ);
    outb(value, PIC1_DATA_PORT);
}

inline void clear_IRQ_mask(uint32_t num_IRQ) {
    unsigned char value = inb(PIC1_DATA_PORT) & ~(1 << num_IRQ);
    outb(value, PIC1_DATA_PORT);
}

inline void init_clock(void) {
    outb(PIT_ONE_SHOT_MODE, PIT_MODECOMMAND_REGISTER);
    outb((QUARTZ / CLOCKFREQ) % 256, PIT_CHANNEL_0_DATA_PORT);
    outb((QUARTZ / CLOCKFREQ) / 256, PIT_CHANNEL_0_DATA_PORT);
}