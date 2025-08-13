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

#pragma once

// The code in this file is intended to be removed once the compiler is properly
// integrated into the client; it's a minimal dummy unsafe implementation of the
// signal-safe assertion mechanism in the client.

#ifdef __cplusplus
extern "C"
{
#endif

void __attribute__((noreturn)) monad_vm_assertion_failed(
    char const *expr, char const *function, char const *file, long line);

#ifdef MONAD_LIKELY
    #define MONAD_VM_LIKELY(x) MONAD_LIKELY(x)
#else
    #define MONAD_VM_LIKELY(x) __builtin_expect(!!(x), 1)
#endif

#ifdef MONAD_UNLIKELY
    #define MONAD_VM_UNLIKELY(x) MONAD_UNLIKELY(x)
#else
    #define MONAD_VM_UNLIKELY(x) __builtin_expect(!!(x), 0)
#endif

#ifdef MONAD_ASSERT
    #define MONAD_VM_ASSERT(expr) MONAD_ASSERT(expr)
#else
    #define MONAD_VM_ASSERT(expr)                                              \
        if (MONAD_VM_LIKELY(expr)) { /* likeliest */                           \
        }                                                                      \
        else {                                                                 \
            monad_vm_assertion_failed(                                         \
                #expr, __extension__ __PRETTY_FUNCTION__, __FILE__, __LINE__); \
        }
#endif

#ifdef MONAD_DEBUG_ASSERT
    #define MONAD_VM_DEBUG_ASSERT(expr) MONAD_DEBUG_ASSERT(expr)
#else
    #ifdef NDEBUG
        #ifdef MONAD_COMPILER_TESTING
            #define MONAD_VM_DEBUG_ASSERT(x) MONAD_VM_ASSERT(x)
        #else
            #define MONAD_VM_DEBUG_ASSERT(x)                                   \
                do {                                                           \
                    (void)sizeof(x);                                           \
                }                                                              \
                while (0)
        #endif
    #else
        #define MONAD_VM_DEBUG_ASSERT(x) MONAD_VM_ASSERT(x)
    #endif
#endif

#ifdef __cplusplus
}
#endif
