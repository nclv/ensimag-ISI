#ifndef __IDT_H__
#define __IDT_H__

#include "inttypes.h"
#include "stdbool.h"

typedef struct idt_entry {
    uint16_t base_lo;           // 16 bits de poids faibles de l’adresse du traitant, bits 0 - 15
    uint16_t segment_selector;  // use with KERNEL_CS from segment.h, bits 16 - 31
    uint16_t flags;             // 0x8E00, bits 32 - 47
    uint16_t base_hi;           // 16 bits de poids forts de l’adresse du traitant, bits 48 - 63
} __attribute__((packed)) idt_entry_t;

typedef struct idt_ptr {
    uint16_t limit;
    uint32_t base;
} __attribute__((packed)) idt_ptr_t;

// named function pointer called interrupt_handler
typedef void (*interrupt_handler_t)(void);

extern void init_idt(void);
extern void masque_IRQ(uint32_t num_IRQ, bool masque);
extern uint32_t get_uptime(void);

// Interrupt handlers
// Extern asm functions defined in traitants.S
extern void traitant_IT_32(void);

#endif