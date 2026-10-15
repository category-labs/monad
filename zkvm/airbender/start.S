/* Airbender guest entry. The machine starts at pc 0, the first word of ROM,
 * in machine mode with every register zero. Set up gp and the stack, then
 * enter the C runtime (runtime.c), which never returns. */
    .section .init, "ax"
    .global _start
_start:
    .option push
    .option norelax
    la gp, __global_pointer$
    .option pop
    la sp, _sstack
    mv s0, sp
    j monad_zkvm_airbender_start
