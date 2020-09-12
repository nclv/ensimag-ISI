/*
 * crt0.S
 *
 * Copyright (C) 2003-2007 by Simon Nieuviarts
 *
 * Kernel entry point.
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
#include "start.h"

	.text
	.comm   first_stack,FIRST_STACK_SIZE,32
	.comm   multiboot_magic,4,4
	.comm   multiboot_info,4,4

	/* The entry point must be before the multiboot header. */
.global entry
entry:
	/* Setup the code segment. */
	jmp	entry2

	/* The multiboot header. */
	.p2align 2
0:	.long	0x1BADB002		/* magic number. */
	.long	0x00010002		/* flags. */
	.long	-0x1BADB002-0x00010002	/* checksum. */
	.long	0b
	.long	_start
	.long	_edata
	.long	__bss_end
	.long	entry

	/*
	 * This global label is here to realign the debugger on the beginning
	 * of the code
	 */
entry2:
	movl	%eax,multiboot_magic	/* It can be verified later. */
	movl	%ebx,multiboot_info	/* It can be used later. */

	/* We have to set up a stack. */
	leal	first_stack,%esp
	addl	$FIRST_STACK_SIZE,%esp
	xorl	%ebp,%ebp

	/* Clear the flags. */
	pushl	$0
	popfl
	/* Note that the Interrupt Flag is cleared : interrupts are disabled. */

	/* Blank all uninitialized memory */
	movl	$_edata,%edi
	xorl	%eax,%eax
0:	movl	%eax,(%edi)
	addl	$4,%edi
	cmpl	$mem_heap_end,%edi
	jb	0b

	/* Setup the processor tables. */
	call	cpu_init

	/* To support C++, should run __CTOR_LIST__ just now */

	/* Jumps into the kernel starting code. */
	call	kernel_start

	/* This function should never exit. */
hang:
	jmp hang

.global setup_pgtab
setup_pgtab:
	/* Setup page tables. The first 16M are mapped for kernel only */
	/* Note that the first page is protected, to catch null pointers */
	leal	pgtab,%eax
	xorl	%edi,%edi
	movl	%edi,(%eax)
	addl	$4,%eax
	movl	$4*1024-1,%edx
	movl	$0x1007,%edi
0:	movl	%edi,(%eax)
	addl	$4,%eax
	addl	$0x1000,%edi
	decl	%edx
	jnz	0b

	/* The next 32M are mapped for user and kernel access */
	movl	$8*1024,%edx
0:	movl	%edi,(%eax)
	addl	$4,%eax
	addl	$0x1000,%edi
	decl	%edx
	jnz	0b

	/* Enable paging */
	leal	pgdir,%eax
	movl	%eax,tss+28
	movl	%eax,%cr3
	movl	%cr0,%eax
	orl	$0x80000000,%eax
	movl	%eax,%cr0
	jmp	0f
0:	movl	$0f,%eax
	jmp	*%eax
0:	ret

/* Unimplemented functions.
You have to implement them it in ".c" files. As these symbols are marked as
"weak", they will no more be used as soon as you write your implementations.
*/
	.weak console_putbytes
console_putbytes:
	ret

	.weak keyboard_data
keyboard_data:
	ret

/* Implement this one only if you want to light LEDs in sync with keyboard's
state. */
	.weak kbd_leds
kbd_leds:
	ret

	.org	0x1000
	.global pgdir
pgdir:
	.long	0x102003
	.long	0x103003
	.long	0x104003
	.long	0x105003
	.long	0x106007
	.long	0x107007
	.long	0x108007
	.long	0x109007
	.long	0x10a007
	.long	0x10b007
	.long	0x10c007
	.long	0x10d007
	.fill	1012,4,0

	.org	0x2000
pgtab:
	.org	0xe000
