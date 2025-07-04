// This function acts as a trampoline to make the interpreter's core loop
// compatible with the existing runtime exit mechanism. It sets up the stack and
// preserved registers so that `monad_vm_runtime_exit` can clean them up in the
// same way as it does for compiled code.
.text
.globl monad_vm_interpreter_trampoline
.type monad_vm_interpreter_trampoline, @function
.align 16
monad_vm_interpreter_trampoline:
.cfi_startproc
    pushq %rbp
    pushq %rbx    
    pushq %r12
    pushq %r13
    pushq %r14
    pushq %r15
    movq %rsp, (%rdi)
    jmp monad_vm_interpreter_core_loop
.cfi_endproc
.size monad_vm_interpreter_trampoline, .-monad_vm_interpreter_trampoline
.section .note.GNU-stack,"",@progbits
