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
[[gnu::always_inline]] static inline void *alloc_or_exit(std::size_t size)
{
    if (size == 0) {
        size = 1;
    }
    void *ptr = sys_alloc_aligned(size, 16);
    if (!ptr) {
        zkvm_halt(1);
    }
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

// The guest links neither libstdc++ nor libsupc++ (the toolchain file passes
// -nostdlib++, and nothing links them back in), so every C++ runtime symbol the
// compiler emits a reference to has to be defined in this file. Exceptions are
// disabled (-fno-exceptions), which is what keeps the list short: the unwinder
// surface (__cxa_throw, __cxa_allocate_exception, __gxx_personality_v0,
// _Unwind_Resume) is never referenced at all. What remains is the handful of
// `std::__throw_*` helpers that libstdc++ containers call on a failed
// precondition, plus the __cxa_* bookkeeping below.
//
// All of those error paths bottom out in abort() — the default
// terminate_handler calls it, GCC's stack protector calls it, etc.
// Newlib's bare-metal abort() ultimately calls _exit() which expects a
// host kernel that the zkVM doesn't have. Route the chain into our
// backend exit hook so every unrecoverable C++ ABI failure surfaces as a
// clean zkvm_halt(1) (= failed proof) rather than a hang/trap.
//
// Weak so the SP1 backend's libzkevm.a, which exports its own strong abort()
// (routed to SP1's halt), wins; on ZisK no other definition exists, so this
// fallback is used.
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

// Emitted into the vtable slot of a pure virtual function; reaching it means a
// pure virtual was called during construction or destruction. Normally supplied
// by libsupc++, which the guest does not link.
[[noreturn]] void __cxa_pure_virtual()
{
    zkvm_halt(1);
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

    // Both are reached from allocating containers: __throw_bad_alloc when the
    // allocator returns null, __throw_bad_array_new_length when an element
    // count times its element size overflows size_t. Referenced only on 32-bit
    // targets (ankerl::unordered_dense's growth path, via State and
    // CommitBuilder) — with a 64-bit size_t GCC proves the overflow check
    // cannot fire against the container's own max_size and folds the call away,
    // whereas a 32-bit size_t makes it a live branch.
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
    // refcount path is dead code in practice (no exception ever gets
    // captured), but std::function's move/copy still emits references to
    // these. No-op bodies suffice — no real exception object exists.
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
