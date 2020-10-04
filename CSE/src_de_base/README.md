# Useful links

 - [The little book about OS development](https://littleosbook.github.io/)
 - [OSDev Tutorial Page](https://wiki.osdev.org/Tutorials)
 - [Kernel Code Source Example](https://github.com/tehybel/osdev/tree/hardware/kern)

# Workflow

Terminal 1
```bash
make
export DISPLAY=0:0  # WSL
make run  # Launch qemu
```

Terminal 2
```bash
gdb kernel.bin
target remote:1234  # Pair with the OS
b kernel_start
bt
c
(s|n|display)
```