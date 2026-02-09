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

// This function acts as a trampoline to make the interpreter's core loop
// compatible with the existing runtime exit mechanism. It sets up the stack and
// preserved registers so that `monad_vm_runtime_exit` can clean them up in the
// same way as it does for compiled code.
.text
.globl monad_vm_interpreter_trampoline
.type monad_vm_interpreter_trampoline, @function
.align 16
monad_vm_interpreter_trampoline:
    pushq %rbp
    pushq %rbx    
    pushq %r12
    pushq %r13
    pushq %r14
    pushq %r15
    movq %rsp, (%rdi)
    pushq %rbp // for stack alignment
    // Use the call instruction to enter the interpreter loop, so that the
    // trampoline is the return address of the interpreter loop. Stack
    // backtraces will deterministically end at the trampoline like this,
    // because the trampoline is not in the `.eh_frame` unwind table.
    call *%r8
    int3 // unreachable
.size monad_vm_interpreter_trampoline, .-monad_vm_interpreter_trampoline
.section .note.GNU-stack,"",@progbits
