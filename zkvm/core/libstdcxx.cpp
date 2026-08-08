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

#include <zkvm/core/arena.hpp>
#include <zkvm/core/libc.hpp>
#include <zkvm/core/zkvm_halt.h>

#include <algorithm>
#include <cstddef>
#include <exception>
#include <memory>
#include <typeinfo>

// operator new / delete
//
// delete never frees memory in the guest. Serve new/new[] from 32 MiB chunks
// (larger for oversized requests) to amortize allocator overhead. When a
// request does not fit, abandon the tail and start a new chunk. The fast path
// is zkvm_arena_alloc in zkvm/core/arena.hpp, shared with other buffers the
// guest never frees.
namespace
{
    constexpr std::size_t ARENA_CHUNK = std::size_t{32} << 20;
}

ZkvmArena zkvm_arena = {nullptr, nullptr};

void *zkvm_arena_alloc_slow(std::size_t size)
{
    unsigned char *next = zkvm_arena.next;
    // Normalize small requests to 16; GCC emits a branchless maxu. Only a
    // zero-byte request can fit after it, and 16 is already rounded.
    size = std::max(size, std::size_t{16});
    if (size > static_cast<std::size_t>(zkvm_arena.end - next)) {
        // Round the required size up to 16, checking for overflow. The check
        // lives here, off the inline fast path, which cannot overflow.
        if (__builtin_add_overflow(size, std::size_t{15}, &size)) {
            zkvm_halt(1);
        }
        size &= ~std::size_t{15};
        // Reserve at least ARENA_CHUNK, or enough for this request.
        std::size_t const chunk = std::max(size, ARENA_CHUNK);
        next = static_cast<unsigned char *>(sys_alloc_aligned(chunk, 16));
        if (!next) {
            zkvm_halt(1);
        }
        zkvm_arena.end = next + chunk;
    }
    // Advance past the allocation and return its start.
    zkvm_arena.next = next + size;
    return next;
}

void *operator new(std::size_t size)
{
    return zkvm_arena_alloc(size);
}

void *operator new[](std::size_t size)
{
    return zkvm_arena_alloc(size);
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

    // Wider buckets make array allocation emit these failure paths.
    // Halt instead of throwing: the guest does not support exceptions.
    [[noreturn]] void __throw_bad_alloc()
    {
        zkvm_halt(1);
    }

    [[noreturn]] void __throw_bad_array_new_length()
    {
        zkvm_halt(1);
    }

    // Exception paths referenced by std::function.
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
