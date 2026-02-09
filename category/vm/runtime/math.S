// Copyright (C) 2025 Category Labs, Inc.
//
// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with this program.  If not, see <http://www.gnu.org/licenses/>.

.text
.intel_syntax noprefix
.globl monad_vm_runtime_mul
.type monad_vm_runtime_mul, @function
.align 16
monad_vm_runtime_mul:
    push    r13
    push    r12
    mov     r8, qword ptr [rdx]
    mov     r9, qword ptr [rdx + 8]
    mov     r10, qword ptr [rdx + 16]
    mov     rax, qword ptr [rsi] 
    mov     r13, rax 
    imul    r13, qword ptr [rdx + 24] 
    mov     rdx, r8 
    mulx    r11, rcx, rax 
    mov     rdx, r9 
    mulx    r12, rdx, rax 
    add     r11, rdx 
    mov     rdx, r10 
    mulx    rax, rdx, rax
    adc     r12, rdx 
    adc     r13, rax 
    mov     qword ptr [rdi], rcx
    mov     rax, qword ptr [rsi + 8] 
    imul    r10, rax 
    mov     rdx, r8 
    mulx    rcx, rdx, rax 
    add     r12, rcx 
    adc     r13, r10 
    add     r11, rdx 
    mov     rdx, r9 
    mulx    rax, rdx, rax 
    adc     r12, rdx 
    adc     r13, rax 
    mov     rax, qword ptr [rsi + 16] 
    imul    r9, rax 
    mov     rdx, r8 
    mulx    rax, rdx, rax 
    add     r13, rax 
    add     r12, rdx 
    adc     r13, r9 
    imul    r8, qword ptr [rsi + 24] 
    add     r13, r8 
    mov     qword ptr [rdi + 8], r11
    mov     qword ptr [rdi + 16], r12
    mov     qword ptr [rdi + 24], r13
    pop     r12
    pop     r13
    ret
.size monad_vm_runtime_mul, .-monad_vm_runtime_mul

.globl monad_vm_runtime_mul_192
.type monad_vm_runtime_mul_192, @function
.align 16
monad_vm_runtime_mul_192:
    mov     r8, qword ptr [rdx]
    mov     r9, qword ptr [rdx + 8]
    mov     r10, qword ptr [rdx + 16]
    mov     rax, qword ptr [rsi]
    mov     rdx, r8
    mulx    r11, rcx, rax
    mov     qword ptr [rdi], rcx
    mov     rdx, r9
    mulx    rcx, rdx, rax
    add     r11, rdx
    mov     rdx, r10
    mulx    rax, rdx, rax
    adc     rcx, rdx
    mov     rax, qword ptr [rsi + 8]
    mov     rdx, r8
    mulx    r10, rdx, rax
    add     rcx, r10
    add     r11, rdx
    mov     rdx, r9
    mulx    rax, rdx, rax
    adc     rcx, rdx
    mov     rax, qword ptr [rsi + 16]
    mov     rdx, r8
    imul    rdx, rax
    add     rcx, rdx
    mov     qword ptr [rdi + 8], r11
    mov     qword ptr [rdi + 16], rcx
    ret
.size monad_vm_runtime_mul_192, .-monad_vm_runtime_mul_192

.section .note.GNU-stack,"",@progbits
