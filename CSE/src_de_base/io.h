#ifndef __IO_H__
#define __IO_H__

#include "inttypes.h"

#define QUARTZ (0x1234DD)
#define CLOCKFREQ (50)

extern void pic_acknowledge(void);
extern void set_cursor(uint16_t pos);
extern void set_IRQ_mask(uint32_t num_IRQ);
extern void clear_IRQ_mask(uint32_t num_IRQ);
extern void init_clock(void);

#endif