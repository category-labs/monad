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

#include <category/core/assert.h>
#include <category/vm/compiler/ir/x86/near_jit_runtime.hpp>
#include <category/vm/runtime/types.hpp>

#include <asmjit/core/codeholder.h>
#include <asmjit/core/globals.h>
#include <asmjit/core/jitallocator.h>
#include <asmjit/core/jitruntime.h>
#include <asmjit/core/virtmem.h>

#include <dlfcn.h>
#include <sys/mman.h>
#include <sys/random.h>

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <cstring>
#include <iterator>
#include <map>
#include <mutex>
#include <unordered_map>
#include <utility>

namespace monad::vm::compiler::native
{
    NearJitRuntime::NearJitRuntime(
        asmjit::JitAllocator::CreateParams const *const params,
        size_t const near_size)
        : asmjit::JitRuntime{params}
        , size_{near_size}
    {
    }

    NearJitRuntime::~NearJitRuntime()
    {
        if (rx_) {
            asmjit::VirtMem::DualMapping dm{rx_, rw_};
            asmjit::VirtMem::releaseDualMapping(&dm, size_);
        }
    }

    // Map the code just below the object holding the runtime functions.
    void NearJitRuntime::map_near()
    {
        Dl_info info;
        if (dladdr(
                reinterpret_cast<void *>(
                    monad_vm_runtime_increase_memory_raw_v1),
                &info) == 0) {
            return;
        }
        // A random page aligned slide below 512 MiB keeps the range away
        // from a fixed offset to the image, still within rel32 reach.
        size_t slide = 0;
        if (getrandom(&slide, sizeof(slide), GRND_NONBLOCK) < 0) {
            slide = 0;
        }
        slide &= (size_t{1} << 29) - (size_t{1} << 12);
        auto const image = reinterpret_cast<uintptr_t>(info.dli_fbase);
        if (image < size_ + slide) {
            return;
        }
        auto *const near = reinterpret_cast<void *>(image - slide - size_);
        void *const reserved = mmap(
            near,
            size_,
            PROT_NONE,
            MAP_PRIVATE | MAP_ANONYMOUS | MAP_NORESERVE | MAP_FIXED_NOREPLACE,
            -1,
            0);
        if (reserved != near) {
            if (reserved != MAP_FAILED) {
                munmap(reserved, size_);
            }
            return;
        }
        asmjit::VirtMem::DualMapping dm;
        if (asmjit::VirtMem::allocDualMapping(
                &dm, size_, asmjit::VirtMem::MemoryFlags::kAccessRWX) !=
            asmjit::kErrorOk) {
            munmap(near, size_);
            return;
        }
        // Move the executable view onto the reserved range.
        if (mremap(dm.rx, size_, size_, MREMAP_MAYMOVE | MREMAP_FIXED, near) !=
            near) {
            munmap(near, size_);
            asmjit::VirtMem::releaseDualMapping(&dm, size_);
            return;
        }
        rx_ = static_cast<std::byte *>(near);
        rw_ = static_cast<std::byte *>(dm.rw);
        // Like asmjit, leave the first granule unused: UBSAN's function
        // check reads the bytes before an entry point.
        free_.emplace(64, size_ - 64);
    }

    asmjit::Error NearJitRuntime::_add(
        void **const dst, asmjit::CodeHolder *const code) noexcept
    {
        *dst = nullptr;
        if (auto const err = code->flatten(); err != asmjit::kErrorOk) {
            return err;
        }
        if (auto const err = code->resolveUnresolvedLinks();
            err != asmjit::kErrorOk) {
            return err;
        }
        // 64 byte granules keep the 64 byte aligned ro section cache line
        // aligned, as with asmjit's allocator.
        std::byte *const rx = allocate((code->codeSize() + 63) & ~size_t{63});
        if (!rx) {
            return asmjit::JitRuntime::_add(dst, code);
        }
        auto const err = code->relocateToBase(reinterpret_cast<uint64_t>(rx));
        if (err != asmjit::kErrorOk) {
            deallocate(rx);
            return err;
        }
        for (asmjit::Section const *const section : code->sections()) {
            std::byte *const rw = rw_ + (rx - rx_) + section->offset();
            std::memcpy(rw, section->data(), section->bufferSize());
            std::memset(
                rw + section->bufferSize(),
                0,
                section->realSize() - section->bufferSize());
        }
        *dst = rx;
        return asmjit::kErrorOk;
    }

    asmjit::Error NearJitRuntime::_release(void *const p) noexcept
    {
        if (!deallocate(p)) {
            return asmjit::JitRuntime::_release(p);
        }
        return asmjit::kErrorOk;
    }

    std::byte *NearJitRuntime::allocate(size_t const size)
    {
        std::lock_guard const lock{mutex_};
        if (std::exchange(map_on_first_add_, false)) {
            map_near();
        }
        auto const it = std::ranges::find_if(
            free_, [=](auto const &f) { return f.second >= size; });
        if (size == 0 || it == free_.end()) {
            return nullptr;
        }
        auto const [offset, free_size] = *it;
        free_.erase(it);
        if (free_size > size) {
            free_.emplace(offset + size, free_size - size);
        }
        used_.emplace(offset, size);
        return rx_ + offset;
    }

    bool NearJitRuntime::deallocate(void *const p)
    {
        std::lock_guard const lock{mutex_};
        auto const offset =
            reinterpret_cast<uintptr_t>(p) - reinterpret_cast<uintptr_t>(rx_);
        if (!rx_ || offset >= size_) {
            return false;
        }
        auto const used = used_.find(offset);
        MONAD_ASSERT(used != used_.end());
        size_t size = used->second;
        used_.erase(used);
        auto next = free_.lower_bound(offset);
        if (next != free_.end() && offset + size == next->first) {
            size += next->second;
            next = free_.erase(next);
        }
        if (next != free_.begin()) {
            auto const prev = std::prev(next);
            if (prev->first + prev->second == offset) {
                prev->second += size;
                return true;
            }
        }
        free_.emplace_hint(next, offset, size);
        return true;
    }
}
