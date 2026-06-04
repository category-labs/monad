/*
 * Overlay for the SP1 SDK's zkvm.ld, passed as a second -T after it.
 *
 * The SDK script is written for Rust guests and has no output sections for
 * .data.rel.ro, .init_array or .got, so ld.lld would place them as orphans
 * after .bss, past `_end` / `_heap_start`, where the SDK allocator's first
 * allocation overwrites them. Insert them ahead of .data instead (ld.lld
 * requires RELRO sections to be contiguous), and expose the .init_array
 * bounds so main.c can run the C++ static constructors that SP1's `_start`
 * does not.
 */

SECTIONS
{
    .data.rel.ro : ALIGN(16)
    {
        *(.data.rel.ro .data.rel.ro.* .gnu.linkonce.d.rel.ro.*)
    }

    .init_array : ALIGN(8)
    {
        __init_array_start = .;
        KEEP(*(SORT_BY_INIT_PRIORITY(.init_array.*)))
        KEEP(*(.init_array))
        __init_array_end = .;
    }

    .got : ALIGN(16)
    {
        *(.got.plt) *(.igot.plt) *(.got) *(.igot)
    }
}
INSERT BEFORE .data;
