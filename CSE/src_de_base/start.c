#include <inttypes.h>
#include <stdio.h>

#include "console.h"
#include "cpu.h"
#include "idt.h"
#include "processus.h"

void init_clock(void);

void kernel_start(void) {
    /*init_console();
    printf("Two aliens in space looking at Earth are talking to each other.\n\nThe first alien says, \"The dominant life forms on the Earth planet have developed satellite-based nuclear weapons.\"\n\nThe second alien asks, \"Are they an emerging intelligence?\"\n\n-\n\nThe first alien says, \"I don't think so, they have them aimed at themselves.");
    // printf("\fa clean one");
    printf("\nA\tB\tC\tD\tE\tF\tG\tH\tI\tJ\tK\tYEESSS");
    printf("\nohohoh\t");
    printf("\nohoh\b\baaaaaahhhh");
    printf("\nohohoh\raaaaaahhhh");
    // clear_console();
    const char* string= "Hello there";
    printf("My string: %s\n", string);
    printf("\rAA");

    clear_console();
    printf("0\n1\n2\n3\n4\n5\n6\n7\n8\n9\n0\n1\n2\n3\n4\n5\n6\n7\n8\n9\n0\n1\n2\n3\n4");
    printf("\t\t\t\tYeahhh\t1\t2\t3\t4\t5\t6");
    printf("Two aliens in space looking at Earth are talking to each other.\n\nThe first alien says, \"The dominant life forms on the Earth planet have developed satellite-based nuclear weapons.\"\n\nThe second alien asks, \"Are they an emerging intelligence?\"\n\n-\n\nThe first alien says, \"I don't think so, they have them aimed at themselves.");
    
    printf("0\n1\n2\n3\n4\n5\n6\n7\n8\n9\n0\n1\n2\n3\n4\n5\n6\n7\n8\n9\n0\n1\n2\n3\n4");
    printf("\t\t\t\tYeahhh\t1\t2\t3\t4\t5\t6");
    printf("Two aliens in space looking at Earth are talking to each other.\n\nThe first alien says, \"The dominant life forms on the Earth planet have developed satellite-based nuclear weapons.\"\n\nThe second alien asks, \"Are they an emerging intelligence?\"\n\n-\n\nThe first alien says, \"I don't think so, they have them aimed at themselves.");
    
    printf("0\n1\n2\n3\n4\n5\n6\n7\n8\n9\n0\n1\n2\n3\n4\n5\n6\n7\n8\n9\n0\n1\n2\n3\n4");
    printf("\t\t\t\tYeahhh\t1\t2\t3\t4\t5\t6");
    printf("Two aliens in space looking at Earth are talking to each other.\n\nThe first alien says, \"The dominant life forms on the Earth planet have developed satellite-based nuclear weapons.\"\n\nThe second alien asks, \"Are they an emerging intelligence?\"\n\n-\n\nThe first alien says, \"I don't think so, they have them aimed at themselves.");
    
    printf("9\n0\n1\n2\n3\n4");
    printf("\t\t\t\tYeahhh\t1\t2\t3\t4\t5\t6");
    printf("Two aliens in space looking at Earth are talking to each other.\n\nThe first alien says, \"The dominant life forms on the Earth planet have developed satellite-based nuclear weapons.\"\n\nThe second alien asks, \"Are they an emerging intelligence?\"\n\n-\n\nThe first alien says, \"I don't think so, they have them aimed at themselves.");
    */
    init_console();

    // cli(); // désactivation/masquage de toutes les interruptions externes

    printf("Initialisation de l'horloge programmable:  ");
    init_clock();
    console_write_color("Success\n", 0);

    printf("Initialisation de la table des vecteurs d'interruption:  ");
    init_idt();
    console_write_color("Success\n", 0);

    printf("Demasquage de l'IRQ0 (clock):  ");
    masque_IRQ(32, 0);
    console_write_color("Success\n", 0);

    printf("Initialisation des processus:  ");
    init_processes();
    console_write_color("Success\n", 0);

    idle();

    // char hour[] = "00:00:00";
    // console_write_hour(hour);

    // sti();  // activation/démasquage des interruptions externes

    // on ne doit jamais sortir de kernel_start
    while (1) {
        /* 
            La fonction hlt() est définie dans cpu.h: elle a pour effet d’endormir le processeur (pour économiser de l’énergie). 
            Le processeur sera réveillé par l’arrivée d’une interruption : il est donc essentiel que les interruptions soient 
            démasquées avant d’appeler cette fonction.
        */
        hlt();
    }
}

int main(void) {
    kernel_start();
    return 0;
}