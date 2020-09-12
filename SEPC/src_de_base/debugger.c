#include "cpu.h"
#include "debug.h"
#include "processor_structs.h"
#include "string.h"

extern unsigned char task_dump_screen[];
static char *screen_base = (char *)0xb8000;

static void write_hex(int line, int col, int length, unsigned long value) {
    char *p = screen_base + ((line - 1) * 160 + (col + length - 1) * 2);
    char disp[16];
    int i;
    for (i = 0; i < 10; i++) disp[i] = '0' + i;
    for (i = 0; i < 6; i++) disp[i + 10] = 'A' + i;
    while (length-- > 0) {
        p -= 2;
        *p = disp[value & 15];
        value >>= 4;
    }
}

static void dump_registers(unsigned trapno, unsigned error_code, struct x86_tss *t) {
    int i, j, k;
    k = 0;
    for (i = 0; i < 25; i++) {
        for (j = 0; j < 80; j++) {
            screen_base[i * 160 + j * 2] = task_dump_screen[k++];
        }
        k++;
    }

    for (i = 0; i < 80 * 25; i++) {
        j = 2 * i + 1;
        screen_base[j] = 0x30;
    }
    for (i = 161; i < 239; i++) {
        j = 2 * i + 1;
        screen_base[j] = 0x34;
    }
    write_hex(7, 21, 2, trapno);
    write_hex(7, 60, 8, error_code);
    write_hex(9, 21, 8, (unsigned long)t);
    write_hex(9, 69, 4, t->back_link);
    write_hex(11, 11, 8, t->esp);
    write_hex(11, 32, 4, t->ss);
    write_hex(11, 52, 8, t->esp0);
    write_hex(11, 74, 4, t->ss0);
    write_hex(13, 11, 8, t->esp1);
    write_hex(13, 32, 4, t->ss1);
    write_hex(13, 52, 8, t->esp2);
    write_hex(13, 74, 4, t->ss2);
    write_hex(15, 15, 8, t->eip);
    write_hex(15, 41, 4, t->cs);
    write_hex(15, 66, 8, t->eflags);
    write_hex(17, 10, 8, t->eax);
    write_hex(17, 30, 8, t->ebx);
    write_hex(17, 50, 8, t->ecx);
    write_hex(17, 70, 8, t->edx);
    write_hex(19, 10, 8, t->esi);
    write_hex(19, 30, 8, t->edi);
    write_hex(19, 50, 8, t->ebp);
    write_hex(19, 72, 4, t->ldt);
    write_hex(21, 12, 4, t->ds);
    write_hex(21, 32, 4, t->es);
    write_hex(21, 52, 4, t->fs);
    write_hex(21, 72, 4, t->gs);
    write_hex(23, 30, 8, t->cr3);
    write_hex(23, 70, 1, t->trace_trap & 1);
}

static struct x86_tss *tss_sel_2_tss(unsigned short sel) {
    unsigned char *pdesc = (unsigned char *)&gdt[sel >> 3];
    unsigned long p = (*(unsigned long *)(pdesc + 2)) & 0xffffff;
    p += ((unsigned long)pdesc[7]) << 24;
    return (struct x86_tss *)p;
}

// Called from the assembly handler tasks
void trap_handler(unsigned trapno, unsigned error_code) {
    unsigned long tr;
    __asm__ __volatile__("str %%eax"
                         : "=a"(tr));
    struct x86_tss *t = tss_sel_2_tss(tss_sel_2_tss(tr)->back_link);

    char d = 1;
    char video_mem[4000];
    memcpy(video_mem, screen_base, sizeof(video_mem));
    dump_registers(trapno, error_code, t);
    while (1) {
        char c = inb(0x60);
        switch (c) {
            case 0x39:  // SPACE
                d = 1 - d;
                if (d) {
                    dump_registers(trapno, error_code, t);
                } else {
                    memcpy(screen_base, video_mem, sizeof(video_mem));
                }
                while (inb(0x60) == 0x39)
                    ;
                break;
        }
    }
}
