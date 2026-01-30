.intel_syntax noprefix

// offsetof(Context, gas_remaining):
#define gas_remaining_offset 16

// offsetof(Context, memory) + offsetof(Memory, size):
#define memory_size_offset (264 + 0)

// offsetof(Context, memory) + offsetof(Memory, capacity):
#define memory_capacity_offset (264 + 4)

// offsetof(Context, memory) + offsetof(Memory, data):
#define memory_data_offset (264 + 8)

// offsetof(Context, memory) + offsetof(Memory, cost):
#define memory_cost_offset (264 + 16)

// offsetof(Context, memory) + offsetof(Memory, data_handle):
#define memory_data_handle_offset (264 + 24)

// Like `runtime::expand_memory`, but no `memory.size < *min_size` check:
.text
.globl monad_vm_runtime_increase_memory_raw_v1
.type monad_vm_runtime_increase_memory_raw_v1, @function
.align 16
monad_vm_runtime_increase_memory_raw_v1:
// Arguments:
//  rbx: Context *ctx
//  edi: Bin<29> min_size
// Scratch registers:
//  rdi, rsi, rcx, rdx,
//  ymm5, ymm6, ..., ymm15
// Callee save registers:
//  rax, rsp, rbp, rbx, r8, r9, ..., r15,
//  ymm0, ymm1, ymm2, ymm3, ymm4
// Note - no need for vzeroupper before calling this function
    // edi = shr_ceil<5>(edi);
    add edi, 0x1f
    shr edi, 5

    // edx = shl<5>(edi); // Bin<30> new_size
    mov edx, edi
    shl edx, 5

    // rsi = memory_cost_from_word_count<...>(edi); // int64_t new_cost
    lea rsi, [rdi + rdi * 2]
    imul rdi, rdi
    shr rdi, 9
    add rsi, rdi

    // rcx = rsi - ctx->memory.cost; // int64_t expansion_cost
    mov rcx, rsi
    sub rcx, [rbx + memory_cost_offset]

    // Gas check before increasing capacity:
    // deduct_gas(rcx);
    sub [rbx + gas_remaining_offset], rcx
    js .out_of_gas_exit

    // ctx->memory.cost = rsi;
    mov [rbx + memory_cost_offset], rsi

    // esi = ctx->memory.size; // uint32_t old_size
    mov esi, [rbx + memory_size_offset]

    // ctx->memory.size = edx;
    mov [rbx + memory_size_offset], edx

    // if (ctx->memory.capacity < edx)
    //     goto .increase_capacity;
    cmp [rbx + memory_capacity_offset], edx
    jb .increase_capacity

    ret

// Like `monad_vm_runtime_increase_memory_raw_v1`, but with MIP-3 max
// memory check and MIP-3 expansion cost:
.globl monad_vm_runtime_increase_memory_raw_mip3
.type monad_vm_runtime_increase_memory_raw_mip3, @function
.align 16
monad_vm_runtime_increase_memory_raw_mip3:
// Arguments:
//  rbx: Context *ctx
//  edi: Bin<29> min_size
// Scratch registers:
//  rdi, rsi, rcx, rdx,
//  ymm5, ymm6, ..., ymm15
// Callee save registers:
//  rax, rsp, rbp, rbx, r8, r9, ..., r15,
//  ymm0, ymm1, ymm2, ymm3, ymm4
// Note - no need for vzeroupper before calling this function
    // edi = shr_ceil<5>(edi);
    add edi, 0x1f
    shr edi, 5

    // edx = shl<5>(edi); // Bin<30> new_size
    mov edx, edi
    shl edx, 5

    // rsi = memory.data - memory.data_handle; // Bin<30> parent_total_size()
    mov rsi, [rbx + memory_data_offset]
    sub rsi, [rbx + memory_data_handle_offset]

    // esi = parent_total_size() + new_size; // Bin<31> total_size
    add esi, edx

    // Bound check before increasing size or capacity:
    // if (*total_size > 8MB)
    //     goto .out_of_gas_exit;
    cmp esi, 8 * 1024 * 1024
    ja .out_of_gas_exit

    // rdi = memory_cost_from_word_count<...>(edi); // int64_t new_cost
    shr edi, 1

    // rcx = rdi - ctx->memory.cost; // int64_t expansion_cost
    mov rcx, rdi
    sub rcx, [rbx + memory_cost_offset]

    // Gas check before increasing size or capacity:
    // deduct_gas(rcx);
    sub [rbx + gas_remaining_offset], rcx
    js .out_of_gas_exit

    // ctx->memory.cost = rdi;
    mov [rbx + memory_cost_offset], rdi

    // esi = ctx->memory.size; // uint32_t old_size
    mov esi, [rbx + memory_size_offset]

    // ctx->memory.size = edx;
    mov [rbx + memory_size_offset], edx

    // if (ctx->memory.capacity < edx)
    //     goto .increase_capacity;
    cmp [rbx + memory_capacity_offset], edx
    jb .increase_capacity

    ret

.increase_capacity:
    mov rdi, rbx

    // rdi: Context *ctx
    // esi: uint32_t old_size
    // edx: Bin<31> new_size

    // Save the non-standard callee save registers
    sub rsp, 5*32 + 5*8 // 16 byte aligned
    vmovups [rsp], ymm0
    vmovups [rsp + 32], ymm1
    vmovups [rsp + 64], ymm2
    vmovups [rsp + 96], ymm3
    vmovups [rsp + 128], ymm4
    mov [rsp + 160], rax
    mov [rsp + 168], r8
    mov [rsp + 176], r9
    mov [rsp + 184], r10
    mov [rsp + 192], r11

    vzeroupper
    call monad_vm_runtime_increase_capacity

    // Restore the non-standard callee save registers
    vmovups ymm0, [rsp]
    vmovups ymm1, [rsp + 32]
    vmovups ymm2, [rsp + 64]
    vmovups ymm3, [rsp + 96]
    vmovups ymm4, [rsp + 128]
    mov rax, [rsp + 160]
    mov r8, [rsp + 168]
    mov r9, [rsp + 176]
    mov r10, [rsp + 184]
    mov r11, [rsp + 192]
    add rsp, 5*32 + 5*8

    ret

.out_of_gas_exit:
    // Tail call the out of gas exit function.
    mov rdi, rbx // rdi = ctx
    vzeroupper
    jmp monad_vm_runtime_context_out_of_gas_exit

.size monad_vm_runtime_increase_memory_raw_v1, .-monad_vm_runtime_increase_memory_raw_v1
.size monad_vm_runtime_increase_memory_raw_mip3, .-monad_vm_runtime_increase_memory_raw_mip3

.globl monad_vm_runtime_increase_memory_v1
.type monad_vm_runtime_increase_memory_v1, @function
.align 16
monad_vm_runtime_increase_memory_v1:
// Arguments:
//  edi: Bin<29> min_size
//  rsi: Context *ctx
// Scratch registers:
//  rdi, rsi, rcx, rdx,
//  ymm5, ymm6, ..., ymm15
// Callee save registers:
//  rax, rsp, rbp, rbx, r8, r9, ..., r15,
//  ymm0, ymm1, ymm2, ymm3, ymm4
// Note - no need for vzeroupper before calling this function
push rbx
mov rbx, rsi
call monad_vm_runtime_increase_memory_raw_v1
pop rbx
ret
.size monad_vm_runtime_increase_memory_v1, .-monad_vm_runtime_increase_memory_v1

.globl monad_vm_runtime_increase_memory_mip3
.type monad_vm_runtime_increase_memory_mip3, @function
.align 16
monad_vm_runtime_increase_memory_mip3:
// Arguments:
//  edi: Bin<29> min_size
//  rsi: Context *ctx
// Scratch registers:
//  rdi, rsi, rcx, rdx,
//  ymm5, ymm6, ..., ymm15
// Callee save registers:
//  rax, rsp, rbp, rbx, r8, r9, ..., r15,
//  ymm0, ymm1, ymm2, ymm3, ymm4
// Note - no need for vzeroupper before calling this function
push rbx
mov rbx, rsi
call monad_vm_runtime_increase_memory_raw_mip3
pop rbx
ret
.size monad_vm_runtime_increase_memory_mip3, .-monad_vm_runtime_increase_memory_mip3

.section .note.GNU-stack,"",@progbits
