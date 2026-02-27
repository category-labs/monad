// Copyright (C) 2025-26 Category Labs, Inc.
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

#ifndef ZKVM_EXIT_H
#define ZKVM_EXIT_H

#ifdef MONAD_ZKVM

    #if defined(MONAD_ZKVM_SP1)
void syscall_halt(unsigned char exit_code) __attribute__((noreturn));
    #endif

    #ifdef __cplusplus
extern "C"
{
    #endif

__attribute__((noreturn)) inline void zkvm_exit(int status)
{
    #if defined(MONAD_ZKVM_ZISK)
    // ZisK: ecall with syscall number 93
    register int a0 __asm__("a0") = status;
    register int a7 __asm__("a7") = 93;
    __asm__ volatile("ecall" : : "r"(a0), "r"(a7));
    __builtin_unreachable();
    #elif defined(MONAD_ZKVM_SP1)
    syscall_halt((unsigned char)status);
    #else
        #error                                                                 \
            "No zkVM exit backend defined (expected MONAD_ZKVM_ZISK or MONAD_ZKVM_SP1)"
    #endif
}

    #ifdef __cplusplus
}
    #endif

#endif // MONAD_ZKVM

#endif // ZKVM_EXIT_H
