OUTPUT_ARCH(riscv)
ENTRY(_start) /* Set the entry point of your program */

_Min_Heap_Size = 0x100;      /* required amount of heap  */
_Min_Stack_Size = 0x100; /* required amount of stack */

MEMORY
{
  IMEM : ORIGIN = 0x20000000, LENGTH = 4K
  DMEM : ORIGIN = 0xF0000000, LENGTH = 4K
}

SECTIONS
{
  /* Place program code (.text section) in I_MEMORY */
  .text :   
  {
    . = ALIGN(4); /* Ensure alignment for instructions */
    *(.text)           /* All .text sections from input files */
    *(.text.*)         /* All .text.xxx sections */
    . = ALIGN(4);
  } > IMEM

  /* Place initialized data (.data section) in D_MEMORY */
  .data :
  {
    . = ALIGN(4);
    *(.data)           /* All .data sections */
    *(.data.*)
    . = ALIGN(4);
  } > DMEM

  /* Place uninitialized data (.bss section) in D_MEMORY */
  .bss :
  {
    . = ALIGN(4);
    _bss_start = .;    /* Symbol marking the start of BSS */
    *(.bss)            /* All .bss sections */
    *(.bss.*)
    . = ALIGN(4);
    _bss_end = .;      /* Symbol marking the end of BSS */
  } > DMEM

  ._user_heap_stack :
  {
    . = ALIGN(8);
    PROVIDE ( end = . );
    PROVIDE ( _end = . );
    . = . + _Min_Heap_Size;
    . = . + _Min_Stack_Size;
    . = ALIGN(8);
  } >DMEM

  _stack_top = ORIGIN(DMEM) + LENGTH(DMEM);
}