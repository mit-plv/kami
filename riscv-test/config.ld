SECTIONS
{
  . = 0x0;
  .text : { *(.text) }
  .data : { *(.data) }
  .bss : { *(.bss) }
}
