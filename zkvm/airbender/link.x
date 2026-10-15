/* Airbender guest layout: code in the 4 MB ROM (common_constants/src/rom.rs),
 * read-only data read in place from ROM, everything writable in RAM above it.
 * RAM is zero at start, so .bss needs no clearing; .data and the RELRO
 * sections (.data.rel.ro, .init_array, .got) are copied from ROM by runtime.c. */
MEMORY
{
  ROM (rx) : ORIGIN = 0, LENGTH = 4M
  RAM (rw) : ORIGIN = 4M, LENGTH = 1020M
}

ENTRY(_start)

SECTIONS
{
  .text : ALIGN(4)
  {
    KEEP(*(.init))
    *(.text .text.*)
  } > ROM

  .rodata : ALIGN(8)
  {
    *(.srodata .srodata.*)
    *(.rodata .rodata.*)
  } > ROM

  .stack (NOLOAD) : ALIGN(16)
  {
    . += 64M;
    _sstack = .;
  } > RAM

  .data : ALIGN(16)
  {
    _sdata = .;
    *(.data.rel.ro .data.rel.ro.*)
    . = ALIGN(8);
    __init_array_start = .;
    KEEP(*(SORT_BY_INIT_PRIORITY(.init_array.*)))
    KEEP(*(.init_array))
    __init_array_end = .;
    *(.got .got.*)
    PROVIDE(__global_pointer$ = . + 0x800);
    *(.sdata .sdata.* .data .data.*)
    . = ALIGN(8);
    _edata = .;
  } > RAM AT > ROM
  _sidata = LOADADDR(.data);

  .bss (NOLOAD) : ALIGN(16)
  {
    *(.sbss .sbss.* .bss .bss.* COMMON)
    . = ALIGN(16);
  } > RAM

  .heap (NOLOAD) : ALIGN(16)
  {
    _sheap = .;
  } > RAM
  _eheap = ORIGIN(RAM) + LENGTH(RAM);

  /DISCARD/ : { *(.eh_frame .eh_frame_hdr .comment .note .note.*) }
}

ASSERT(_sidata + (_edata - _sdata) <= 4M, "Airbender: code and data exceed the 4 MB ROM")
