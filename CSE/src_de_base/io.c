#include "io.h"

#include "cpu.h"

#define PIC1_PORT_A (0x20)
#define PIC_ACK (0x20)

/** pic_acknowledge:
  * Acknowledges an interrupt from PIC 1.
  * Send the byte 0x20 to PIC 1 that raised the interrupt. 
  *
  *  @param num The number of the interrupt
*/
void pic_acknowledge(void) {
    outb(PIC_ACK, PIC1_PORT_A);
}