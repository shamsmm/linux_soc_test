.equ GPIO_BASE,     0x30000000
.equ GPIO_OUTPUT,   0x0C
.equ GPIO_OUTPUT_EN, 0x08

_start:
    lui t0, %hi(GPIO_BASE)
    addi t0, t0, %lo(GPIO_BASE)
    li t1, 0b11111100
    sw t1, GPIO_OUTPUT_EN(t0)
    j _start
    