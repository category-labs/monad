/* The build's identity marker (zkvm/guest/build_identity.cpp) is referenced by
   no code, so nothing would pull its object out of the guest archive: ask for
   its symbol. Both profiles define it. */
EXTERN(monad_zkvm_official_profile)

/* Force 8-byte alignment for all sections — required by the ZisK VM. */
SECTIONS {
    .srodata.cst4 : ALIGN(8) {
        *(.srodata.cst4)
    }
    .monad_zkvm_profile : ALIGN(8) {
        KEEP(*(.monad_zkvm_profile))
    }
} INSERT AFTER .rodata;
