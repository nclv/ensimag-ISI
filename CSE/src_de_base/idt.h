#ifndef __IDT_H__
#define __IDT_H__

typedef struct idt_entry {
    uint16_t base_lo;  // 16 bits de poids faibles de l’adresse du traitant
    uint16_t segment_selector;  // use with KERNEL_CS from segment.h
    uint16_t flags;  // 0x8E00
    uint16_t base_hi;  // 16 bits de poids forts de l’adresse du traitant
} __attribute__((packed)) idt_entry_t;

// Extern asm functions
extern void traitant_IT_32(void);

#endif