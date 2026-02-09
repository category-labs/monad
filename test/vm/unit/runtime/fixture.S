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