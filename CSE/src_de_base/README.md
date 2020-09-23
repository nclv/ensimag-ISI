# Workflow

Terminal 1
```bash
make
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