ENTRY(main)
MEMORY
{
  MEM (xrw) : ORIGIN = 0x0, LENGTH = 0x800
}
stack_size = 64;

_stack_start = ORIGIN(MEM)+LENGTH(MEM);
_stack_end = _stack_start - stack_size;

SECTIONS {
 .text 0x0 :
   { . = ALIGN(4);
     *(.text)
     . = ALIGN(4);
   }>MEM
 .data :
   { . = ALIGN(4);
     *(.data)
     . = ALIGN(4);
   }>MEM
 .bss : { *(.bss) *(COMMON) }>MEM
}
