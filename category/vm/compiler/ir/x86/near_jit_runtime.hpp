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

#pragma once

#include <asmjit/core/codeholder.h>
#include <asmjit/core/globals.h>
#include <asmjit/core/jitallocator.h>
#include <asmjit/core/jitruntime.h>

#include <cstddef>
#include <map>
#include <mutex>
#include <unordered_map>

namespace monad::vm::compiler::native
{
    /// JIT runtime that places code within rel32 range of the VM runtime
    /// functions when it can, so that calls into the runtime are direct.
    class NearJitRuntime : public asmjit::JitRuntime
    {
    public:
        explicit NearJitRuntime(
            asmjit::JitAllocator::CreateParams const * = nullptr,
            size_t near_size = size_t{1} << 30);
        ~NearJitRuntime() override;

    protected:
        asmjit::Error _add(void **, asmjit::CodeHolder *) noexcept override;
        asmjit::Error _release(void *) noexcept override;

    private:
        void map_near();
        std::byte *allocate(size_t);
        bool deallocate(void *);

        std::mutex mutex_;
        bool map_on_first_add_{true};
        std::byte *rx_{};
        std::byte *rw_{};
        size_t size_;
        std::map<size_t, size_t> free_;
        std::unordered_map<size_t, size_t> used_;
    };
}
