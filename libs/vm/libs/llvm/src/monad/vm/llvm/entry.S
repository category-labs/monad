// This function acts as a trampoline to make the llvm backend's exit
// compatible with the existing runtime exit mechanism. It sets up the stack and
// preserved registers so that `monad_runtime_exit` can clean them up in the
// same way as it does for compiled code.
.text
.globl llvm_runtime_trampoline
.type llvm_runtime_trampoline, @function
.align 16
llvm_runtime_trampoline:
.cfi_startproc
    pushq %rbp
    pushq %rbx
    pushq %r12
    pushq %r13
    pushq %r14
    pushq %r15
    // rdi contains first argument to contract function
    // rsi contains second argument to contract function
    movq %rsp, (%rcx) // save stack ptr (adjust rdx if args added to contract function)
    jmp *%rdx // jump to contract function (adjust rsi if args added to contract function)
.cfi_endproc
.size llvm_runtime_trampoline, .-llvm_runtime_trampoline
.section .note.GNU-stack,"",@progbits
