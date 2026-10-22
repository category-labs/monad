/* Force 8-byte alignment for all sections — required by the ZisK VM. */
SECTIONS {
    .srodata.cst4 : ALIGN(8) {
        *(.srodata.cst4)
    }
    .monad_zkvm_commit : ALIGN(8) {
        KEEP(*(.monad_zkvm_commit))
    }
} INSERT AFTER .rodata;
