# stub PXE : necessaire pour le demarrage via QEmu
PXE = boot.pxe

# noyau
KERNEL = kernel.bin

# on compile tous les fichiers assembleur et c du repertoire
SRCS = $(wildcard *.S *.c)

# C_SOURCES = $(wildcard kernel/*.c drivers/*.c cpu/*.c libc/*.c)
# HEADERS = $(wildcard kernel/*.h drivers/*.h cpu/*.h libc/*.h)
# Nice syntax for file extension replacement
# OBJ = ${C_SOURCES:.c=.o cpu/interrupt.o} 

# crt0.o doit etre linke en premier
OBJS = $(strip crt0.o $(filter-out crt0.o,$(notdir $(patsubst %.S,%.o,$(patsubst %.c,%.o,$(SRCS))))))

CC = gcc
AS = gcc
LD = ld
OBJCOPY = objcopy
QEMU = /usr/bin/qemu-system-i386

CFLAGS = -m32 -Wall -Werror -gstabs -std=c99 -Wextra -Wno-implicit-fallthrough  -Wshadow -Wconversion -Wdouble-promotion -Wformat=2 -Wformat-truncation=2 -Wundef -fno-common -fstack-usage -Wfloat-equal -Wpointer-arith -Wcast-align -Wstrict-prototypes -Wstrict-overflow=4 -Wwrite-strings -Waggregate-return -ffunction-sections -Wl,--gc-sections -Wl,--print-gc-sections -nostdlib -nostdinc -ffreestanding -fpic -fno-builtin -fno-stack-protector -nostartfiles -nodefaultlibs -I. -ggdb
ASFLAGS = -m32 -DASSEMBLER -g -gstabs -I.
LDFLAGS = -melf_i386
# QEMUOPTS = -no-kvm -net nic -net user,tftp="`pwd`",bootfile="$(PXE)" -boot n -cpu pentium -rtc base=localtime -m 64M -gdb tcp::1234 -S
QEMUOPTS = -cpu pentium -rtc base=localtime -m 64M -gdb tcp::1234 -S -kernel kernel.bin

# cible principale, on nettoie systematiquement le repertoire avant
.PHONY: all
all: clean kernel.bin

# Generic rules for wildcards
# To make an object, always compile from its .c
# %.o: %.c ${HEADERS}
# 	${CC} ${CFLAGS} -ffreestanding -c $< -o $@

# ecran affichant les exceptions
task_dump_screen.o: empty.o task_dump_screen.txt
	$(OBJCOPY) empty.o --add-section=.task_dump_screen=task_dump_screen.txt --set-section-flags=.task_dump_screen=contents,alloc,load,data task_dump_screen.o

# generation du noyau
kernel.bin: kernel.lds $(OBJS) task_dump_screen.o
	$(LD) $(LDFLAGS) -e entry -Tkernel.lds $(OBJS) task_dump_screen.o -o $@

clean:
	$(RM) $(OBJS) $(KERNEL) task_dump_screen.o *.su

run:
	$(QEMU) $(QEMUOPTS)

