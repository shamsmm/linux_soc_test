.section .text
.globl _start

_start:
    li x1, 0xF0000050
    addi x10, x0, 10    # x10 = 10
    sb x10, 0 (x1)
    addi x11, x0, 20    # x11 = 20
    sb x11, 1 (x1)
    add x12, x10, x11   # x12 = x10 + x11 (30)
    sw x12, 4 (x1)
    sub x13, x11, x10   # x13 = x11 - x10 (10)
    sh x13, 6 (x1)
    lw x14, 0 (x1)
    beq x12, x0, .loop  # Branch if x12 == 0 (won't happen)
    j .loop             # Unconditional jump to .loop

.loop:
    # Infinite loop
    j .loop