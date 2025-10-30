// fixture.S
.text
.globl tests_trampoline
.type tests_trampoline, @function
.align 16
tests_trampoline:
    pushq %rbp
    pushq %rbx
    pushq %r12
    pushq %r13
    pushq %r14
    pushq %r15
    movq %rsp, (%rdi)      # save host stack pointer
    pushq %rbp             # 16-byte align the stack
    movq %rdx, %rdi        # move lambda ptr into rdi (first arg for call_closure)
    call *%rsi             # call call_closure (second arg)
    int3                   # This instruction should never be reached: call_closure is expected to exit via ctx->exit()