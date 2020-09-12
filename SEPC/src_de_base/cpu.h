/*
 * cpu.h
 *
 * Copyright (C) 2001 by Simon Nieuviarts
 *
 * CPU specific instructions.
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version. 
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
 */
#ifndef __CPU_H__
#define __CPU_H__

#define __MOVSB__(dest, src, n)          \
    __asm__ __volatile__(                \
        "rep\n"                          \
        "\tmovsb"                        \
        : "=S"(src), "=D"(dest), "=c"(n) \
        : "0"(src), "1"(dest), "2"(n)    \
        : "memory", "cc")

#define __MOVSL__(dest, src, n)          \
    __asm__ __volatile__(                \
        "rep\n"                          \
        "\tmovsl"                        \
        : "=S"(src), "=D"(dest), "=c"(n) \
        : "0"(src), "1"(dest), "2"(n)    \
        : "memory", "cc")

static void __inline__ cli(void) {
    __asm__ __volatile__("cli" ::
                             : "memory");
}

static void __inline__ sti(void) {
    __asm__ __volatile__("sti" ::
                             : "memory");
}

static void __inline__ hlt(void) {
    __asm__ __volatile__("hlt" ::
                             : "memory");
}

static unsigned long __inline__ save_flags(void) {
    unsigned long flags;

    __asm__ __volatile__(
        "pushfl\n"
        "\tpopl	%0\n"
        : "=g"(flags)
        :
        : "memory");

    return flags;
}

static void __inline__ restore_flags(unsigned long flags) {
    __asm__ __volatile__(
        "pushl	%0\n"
        "\tpopfl\n"
        :
        : "g"(flags)
        : "memory");
}

static void __inline__ outb(unsigned char value, unsigned short port) {
    __asm__ __volatile__("outb %0, %1"
                         :
                         : "a"(value), "Nd"(port));
}

static void __inline__ outw(unsigned short value, unsigned short port) {
    __asm__ __volatile__("outw %0, %1"
                         :
                         : "a"(value), "Nd"(port));
}

static void __inline__ outl(unsigned long value, unsigned short port) {
    __asm__ __volatile__("outl %0, %1"
                         :
                         : "a"(value), "Nd"(port));
}

static unsigned char __inline__ inb(unsigned short port) {
    unsigned char rega;
    __asm__ __volatile__("inb %1,%0"
                         : "=a"(rega)
                         : "Nd"(port));
    return rega;
}

static unsigned short __inline__ inw(unsigned short port) {
    unsigned short rega;
    __asm__ __volatile__("inw %1,%0"
                         : "=a"(rega)
                         : "Nd"(port));
    return rega;
}

static unsigned long __inline__ inl(unsigned short port) {
    unsigned long rega;
    __asm__ __volatile__("inl %1,%0"
                         : "=a"(rega)
                         : "Nd"(port));
    return rega;
}

#endif
