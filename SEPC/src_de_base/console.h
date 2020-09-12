#ifndef __CONSOLE_H__
#define __CONSOLE_H__

#include <inttypes.h>

/*
 * This is the function called by printf to send its output to the screen. You
 * have to implement it in the kernel and in the user program.
 */
extern void console_putbytes(const char *s, int len);
extern void terminal_writestring(const char* data);
extern void place_curseur(uint32_t lig, uint32_t col);
extern void enable_cursor(uint8_t cursor_start, uint8_t cursor_end);
extern void init_terminal(void);

#endif
