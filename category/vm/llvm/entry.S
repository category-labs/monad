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

// This function acts as a trampoline to make the llvm backend's exit
// compatible with the existing runtime exit mechanism. It sets up the stack and
// preserved registers so that `monad_runtime_exit` can clean them up in the
// same way as it does for compiled code.
.text
.globl llvm_runtime_trampoline
.type llvm_runtime_trampoline, @function
.align 16
llvm_runtime_trampoline:
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
.size llvm_runtime_trampoline, .-llvm_runtime_trampoline
.section .note.GNU-stack,"",@progbits
