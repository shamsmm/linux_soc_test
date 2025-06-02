.section .text
.globl _start

_start:
    addi x10, x0, 10    # x10 = 10
    addi x11, x0, 20    # x11 = 20
    add x12, x10, x11   # x12 = x10 + x11 (30)
    sub x13, x11, x10   # x13 = x11 - x10 (10)
    beq x12, x0, .loop  # Branch if x12 == 0 (won't happen)
    j .loop             # Unconditional jump to .loop

.loop:
    # Infinite loop
    j .loop