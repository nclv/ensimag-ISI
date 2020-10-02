#ifndef __IO_H__
#define __IO_H__

#include "inttypes.h"

extern void pic_acknowledge(void);
extern void set_cursor(uint16_t pos);

#endif