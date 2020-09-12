#include <cpu.h>
#include <inttypes.h>

#include "console.h"

// on peut s'entrainer a utiliser GDB avec ce code de base
// par exemple afficher les valeurs de x, n et res avec la commande display

// une fonction bien connue
uint32_t fact(uint32_t n) {
    uint32_t res;
    if (n <= 1) {
        res = 1;
    } else {
        res = fact(n - 1) * n;
    }
    return res;
}

void kernel_start(void) {
    uint32_t x = fact(5);
    // quand on saura gerer l'ecran, on pourra afficher x
    (void)x;

    init_terminal();
    terminal_writestring("Two aliens in space looking at Earth are talking to each other.\n\nThe first alien says, \"The dominant life forms on the Earth planet have developed satellite-based nuclear weapons.\"\n\nThe second alien asks, \"Are they an emerging intelligence?\"\n\n-\n\nThe first alien says, \"I don't think so, they have them aimed at themselves.");
    terminal_writestring("\fa clean one");
    terminal_writestring("\nA\tB\tC\tD\tE\tF\tG\tH\tI\tJ\tK\tYEESSS");
    terminal_writestring("\nohohoh\t");
    // terminal_writestring("\nohoh\b\baaaaaahhhh");
    // terminal_writestring("\nohohoh\raaaaaahhhh");
    
    // uint8_t *ptr = (uint8_t *)0xB8000;
    // *ptr = 'H';
    // *(ptr + 1) = 'E';
    // *(ptr + 2) = 'L';
    // *(ptr + 3) = 'L';
    // *(ptr + 4) = 'O';

    // on ne doit jamais sortir de kernel_start
    while (1) {
        // cette fonction arrete le processeur
        hlt();
    }
}
