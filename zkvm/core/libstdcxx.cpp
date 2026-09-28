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

// Minimal C++ runtime stubs for bare-metal zkVM.

#include <zkvm/core/libc.hpp>
#include <zkvm/core/zkvm_halt.h>

#include <cstddef>
#include <exception>
#include <memory>
#include <typeinfo>

// operator new / delete
//
// delete never frees memory in the guest. Serve new/new[] from 32 MiB chunks
// (larger for oversized requests) to amortize allocator overhead. When a
// request does not fit, abandon the tail and start a new chunk.
namespace
{
    constexpr std::size_t ARENA_CHUNK = std::size_t{32} << 20;
    unsigned char *g_arena_cur = nullptr;
    std::size_t g_arena_left = 0;
}

[[gnu::always_inline]] static inline void *alloc_or_exit(std::size_t size)
{
    // g_arena_left is always a multiple of 16 -- every chunk is one, and every
    // request takes one from it -- so a request fits exactly when its size
    // rounded up to 16 does, and the size can be tested before it is rounded.
    // That keeps the rounding's overflow check on the new-chunk path, the only
    // one a size within 15 of SIZE_MAX can take. Checked on entry instead, its
    // halt is reachable before any other call, and gcc sets up the frame on
    // every allocation rather than on that path. A zero-byte request wraps
    // size - 1, so it comes here too, and is served like a one-byte one.
    if (size - 1 >= g_arena_left) {
        if (size == 0) {
            size = 1;
        }
        if (size > g_arena_left) {
            // Add 15, checking for overflow, then round down to a multiple of
            // 16: the size this chunk has to hold.
            std::size_t rounded;
            if (__builtin_add_overflow(size, std::size_t{15}, &rounded)) {
                zkvm_halt(1);
            }
            rounded &= ~std::size_t{15};
            // Reserve ARENA_CHUNK for future allocations, or size if larger.
            std::size_t const chunk =
                rounded > ARENA_CHUNK ? rounded : ARENA_CHUNK;
            g_arena_cur =
                static_cast<unsigned char *>(sys_alloc_aligned(chunk, 16));
            if (!g_arena_cur) {
                zkvm_halt(1);
            }
            g_arena_left = chunk;
        }
    }
    // Round down to a multiple of 16 to keep subsequent allocations aligned.
    // Adding 15 first rounds the original size up, leaving multiples of 16
    // unchanged. size <= g_arena_left here, so the addition cannot wrap.
    size = (size + 15) & ~std::size_t{15};
    // Save the allocation's start, then advance to the next free address.
    void *const ptr = g_arena_cur;
    g_arena_cur += size;
    g_arena_left -= size;
    return ptr;
}

void *operator new(std::size_t size)
{
    return alloc_or_exit(size);
}

void *operator new[](std::size_t size)
{
    return alloc_or_exit(size);
}

void operator delete(void *) noexcept {}

void operator delete[](void *) noexcept {}

void operator delete(void *, std::size_t) noexcept {}

void operator delete[](void *, std::size_t) noexcept {}

// Weak since SP1 backend's libzkevm.a, exports its own strong abort()
// on ZisK no other definition exists, so this fallback is used.
extern "C" [[gnu::weak]] [[noreturn]] void abort() noexcept
{
    zkvm_halt(1);
}

extern "C"
{
void *__dso_handle = nullptr;

int __cxa_atexit(void (*)(void *), void *, void *)
{
    return 0;
}

// Thread-local dtor registration — no threads, nothing to run at exit.
int __cxa_thread_atexit(void (*)(void *), void *, void *)
{
    return 0;
}

// Function-local static init guards. Single-threaded: acquire iff the low
// byte is still zero; release sets it.
int __cxa_guard_acquire(long long *g)
{
    return !*reinterpret_cast<char *>(g);
}

void __cxa_guard_release(long long *g)
{
    *reinterpret_cast<char *>(g) = 1;
}

void __cxa_guard_abort(long long *) {}
}

namespace std
{
    [[noreturn]] void terminate() noexcept
    {
        zkvm_halt(1);
    }

    [[noreturn]] void __throw_length_error(char const *)
    {
        zkvm_halt(1);
    }

    [[noreturn]] void __throw_logic_error(char const *)
    {
        zkvm_halt(1);
    }

    // The allocation-overflow arms of operator new[]: a bucket array whose
    // element is 16 bytes rather than 8 makes `count * sizeof(T)` wide enough
    // that gcc stops proving it cannot overflow and emits the check. Neither is
    // reachable -- the guest's allocator halts on exhaustion long before a
    // count that large -- and both halt for the same reason every stub here
    // does.
    [[noreturn]] void __throw_bad_alloc()
    {
        zkvm_halt(1);
    }

    [[noreturn]] void __throw_bad_array_new_length()
    {
        zkvm_halt(1);
    }

    // Pulled in via std::function — its call operator's empty-target path
    // and rethrow_exception in <functional>'s move/copy plumbing.
    [[noreturn]] void __throw_bad_function_call()
    {
        zkvm_halt(1);
    }

    [[noreturn]] void rethrow_exception(exception_ptr)
    {
        zkvm_halt(1);
    }

    // std::exception_ptr is refcounted. With exceptions disabled the
    // refcount path is dead code in practice but std::function's move/copy
    // still emits references to these.
    namespace __exception_ptr
    {
        void exception_ptr::_M_addref() noexcept {}

        void exception_ptr::_M_release() noexcept {}
    }

    bool _Sp_make_shared_tag::_S_eq(type_info const &) noexcept
    {
        return false;
    }
}
