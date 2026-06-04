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

// zkVM shadow of category/vm/vm.hpp (Decision 5 of the zippy-sifakis plan).
//
// The host VM holds `Compiler compiler_` by value, which transitively pulls
// in TBB, asmjit, and threading primitives — none of which link in the
// bare-metal RISC-V build. This shadow keeps only the surface that the
// witness-execution path actually uses: an interpreter-only execute path
// and the MemoryPool for message-buffer allocation. The varcode cache is
// dropped entirely; find_varcode returns nullopt and the try_insert_varcode
// helpers construct a fresh Varcode each call. A single block's working
// set is tiny enough that re-decoding bytecode per lookup is fine, and not
// sharing across the block keeps the shadow free of any hash-map dep.
//
// Drops vs. the host VM, by callsite audit: Mode/all_modes/mode_to_string
// are only referenced by drivers and tests; CompilerConfig / compiler_config()
// is read only by the host's execute_raw which we replace; the *_raw
// templates and stat printers are private implementation details with no
// external callers.

#pragma once

#include <category/core/bytes.hpp>
#include <category/vm/code.hpp>
#include <category/vm/evm/traits.hpp>
#include <category/vm/host.hpp>
#include <category/vm/interpreter/execute.hpp>
#include <category/vm/interpreter/intercode.hpp>
#include <category/vm/memory_pool.hpp>
#include <category/vm/runtime/allocator.hpp>
#include <category/vm/runtime/types.hpp>

#include <evmc/evmc.h>
#include <evmc/evmc.hpp>

#include <cstdint>
#include <optional>
#include <span>

namespace monad::vm
{
    class VM
    {
        runtime::EvmStackAllocator stack_allocator_;
        MemoryPool memory_pool_;

    public:
        VM()
            : stack_allocator_{}
            , memory_pool_{8 * 1024 * 1024}
        {
        }

        std::optional<SharedVarcode> find_varcode(bytes32_t const &)
        {
            return std::nullopt;
        }

        SharedVarcode
        try_insert_varcode(bytes32_t const &, SharedIntercode const &icode)
        {
            return std::make_shared<Varcode>(icode);
        }

        SharedVarcode try_insert_varcode_raw(
            bytes32_t const &, std::span<uint8_t const> const code)
        {
            return std::make_shared<Varcode>(make_shared_intercode(code));
        }

        MemoryPool::Ref message_memory_ref()
        {
            return memory_pool_.alloc_ref();
        }

        uint32_t message_memory_capacity()
        {
            return memory_pool_.alloc_capacity();
        }

        template <Traits traits>
        evmc::Result execute(
            Host &host, evmc_message const *const msg,
            bytes32_t const & /*code_hash*/, SharedVarcode const &vcode)
        {
            auto const &icode = vcode->intercode();
            auto rt_ctx = runtime::Context::from(
                &host.get_interface(),
                host.to_context(),
                msg,
                icode->code_span());

            auto *const prev_rt_ctx = host.set_runtime_context(&rt_ctx);
            auto const stack_ptr = stack_allocator_.allocate();
            interpreter::execute<traits>(rt_ctx, *icode, stack_ptr.get());
            auto result = rt_ctx.template copy_to_evmc_result<traits>();
            rt_ctx.template return_to<traits>(prev_rt_ctx);
            (void)host.set_runtime_context(prev_rt_ctx);
            host.rethrow_on_active_exception();
            return result;
        }

        template <Traits traits>
        evmc::Result execute_bytecode(
            Host &host, evmc_message const *const msg,
            std::span<uint8_t const> const code)
        {
            auto rt_ctx = runtime::Context::from(
                &host.get_interface(), host.to_context(), msg, code);

            auto *const prev_rt_ctx = host.set_runtime_context(&rt_ctx);
            auto const stack_ptr = stack_allocator_.allocate();
            interpreter::execute<traits>(
                rt_ctx, interpreter::Intercode{code}, stack_ptr.get());
            auto result = rt_ctx.template copy_to_evmc_result<traits>();
            rt_ctx.template return_to<traits>(prev_rt_ctx);
            (void)host.set_runtime_context(prev_rt_ctx);
            host.rethrow_on_active_exception();
            return result;
        }
    };
}
