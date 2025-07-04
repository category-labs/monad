.intel_syntax noprefix

.text
.globl monad_vm_runtime_load_bounded_le_raw
.type monad_vm_runtime_load_bounded_le_raw, @function
.align 16
monad_vm_runtime_load_bounded_le_raw:
// Arguments:
//  rdi: uint8_t const *src_buffer
//  rsi: int64_t load_size
// Returns: ymm15
// Scratch registers:
//  rdi, rsi, rcx, rdx,
//  ymm14, ymm15
// Callee save registers:
//  rsp, rbp, rbx, r12, r13, r14, r15,
//  ymm0, ymm1, ..., ymm13
// Note it is assumed that rsi <= 32
.cfi_startproc
    cmp esi, 16
    jg .g16
    cmp esi, 8
    jg .g8
    cmp esi, 4
    jg .g4
    cmp esi, 2
    jg .g2
    cmp esi, 1
    jg .g1
    je .e1
    vpxor ymm15, ymm15, ymm15
    ret

.g16:
    // 16 < rsi <= 32
    vmovups xmm14, [rdi]
    mov rdx, [rdi + rsi - 16]
    mov rdi, [rdi + rsi - 8]
    xor ecx, ecx
    cmp rsi, 25
    cmovb rdx, rdi
    cmovb rdi, rcx
    mov ecx, 32
    sub ecx, esi
    shl ecx, 3
    shrd rdx, rdi, cl
    shrx rdi, rdi, rcx
    vmovq xmm15, rdx
    vpinsrq xmm15, xmm15, rdi, 1
    vinserti128 ymm15, ymm14, xmm15, 1
    ret

.g8:
    // 8 < rsi <= 16
    vmovq xmm15, [rdi]
    mov rdx, [rdi + rsi - 8]
    mov ecx, 16
    sub ecx, esi
    shl ecx, 3
    shrx rdx, rdx, rcx
    vpinsrq xmm15, xmm15, rdx, 1
    ret

.g4:
    // 4 < rsi <= 8
    vmovd xmm15, [rdi]
    mov edx, [rdi + rsi - 4]
    mov ecx, 8
    sub ecx, esi
    shl ecx, 3
    shrx edx, edx, ecx
    vpinsrd xmm15, xmm15, edx, 1
    ret

.g2:
    // 2 < rsi <= 4
    mov dx, [rdi]
    movzx edx, dx
    mov di, [rdi + rsi - 2]
    movzx edi, di
    mov ecx, 4
    sub ecx, esi
    shl ecx, 3
    shrx edi, edi, ecx
    shl edi, 16
    or edx, edi
    vmovd xmm15, edx
    ret

.g1:
    // rsi == 2
    mov dx, [rdi]
    movzx edx, dx
    vmovd xmm15, edx
    ret

.e1:
    // rsi == 1
    mov dl, [rdi]
    movzx edx, dl
    vmovd xmm15, edx
    ret

.cfi_endproc
.size monad_vm_runtime_load_bounded_le_raw, .-monad_vm_runtime_load_bounded_le_raw

.globl monad_vm_runtime_load_bounded_le
.type monad_vm_runtime_load_bounded_le, @function
.align 16
monad_vm_runtime_load_bounded_le:
// Arguments:
//  rdi: uint8_t const *src_buffer
//  rsi: int64_t load_size
// Returns: ymm0
// Scratch registers:
//  rdi, rsi, rcx, rdx,
//  ymm0, ymm14, ymm15
// Callee save registers:
//  rsp, rbp, rbx, r12, r13, r14, r15,
//  ymm1, ymm2, ..., ymm13
// Note it is assumed that rsi <= 32
.cfi_startproc
call monad_vm_runtime_load_bounded_le_raw
vmovups ymm0, ymm15
ret
.cfi_endproc
.size monad_vm_runtime_load_bounded_le, .-monad_vm_runtime_load_bounded_le

.section .note.GNU-stack,"",@progbits
