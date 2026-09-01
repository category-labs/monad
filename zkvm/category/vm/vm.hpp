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
// helpers construct a fresh Varcode each call.
//
// That last part is measurably wrong, and MONAD_ZKVM_VARCODE_CACHE fixes it. Nothing is re-DECODED --
// BlockState::code_ holds the SharedIntercode, so an intercode is built once per contract per block
// (FINDINGS 85 records mistaking this stub for a scanning gap; the scan is not the cost). What
// repeats is the allocation: State::read_code fills State::code_ only from set_code, so every read of
// an existing contract falls through to BlockState::read_code, misses find_varcode, and builds a
// fresh Varcode and shared_ptr control block out of an intercode it already had.
//
// The VM outlives the block, so one map keyed by code hash removes that per-call allocation. The
// "keeps the shadow free of any hash-map dep" argument does not hold either: unordered_dense is
// already a link dependency of the guest target.
//
// Drops vs. the host VM, by callsite audit: Mode/all_modes/mode_to_string
// are only referenced by drivers and tests; CompilerConfig / compiler_config()
// is read only by the host's execute_raw which we replace; the *_raw
// templates and stat printers are private implementation details with no
// external callers.

#pragma once

#include <category/core/bytes.hpp>
#if defined(MONAD_ZKVM_VARCODE_CACHE)
    #include <ankerl/unordered_dense.h>
#endif
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
#if defined(MONAD_ZKVM_VARCODE_CACHE)
        // One entry per distinct contract the block touches -- the same bound BlockState::code_
        // already lives with for intercodes, so this adds no new lifetime question.
        ankerl::unordered_dense::map<bytes32_t, SharedVarcode> varcode_{};
#endif

    public:
        VM()
            : stack_allocator_{}
            , memory_pool_{8 * 1024 * 1024}
        {
        }

#if defined(MONAD_ZKVM_VARCODE_CACHE)
        std::optional<SharedVarcode> find_varcode(bytes32_t const &code_hash)
        {
            auto const it = varcode_.find(code_hash);
            if (it == varcode_.end()) {
                return std::nullopt;
            }
            return it->second;
        }

        SharedVarcode try_insert_varcode(
            bytes32_t const &code_hash, SharedIntercode const &icode)
        {
            auto const [it, inserted] = varcode_.try_emplace(code_hash, nullptr);
            if (inserted) {
                it->second = std::make_shared<Varcode>(icode);
            }
            return it->second;
        }

        SharedVarcode try_insert_varcode_raw(
            bytes32_t const &code_hash, std::span<uint8_t const> const code)
        {
            auto const [it, inserted] = varcode_.try_emplace(code_hash, nullptr);
            if (inserted) {
                it->second =
                    std::make_shared<Varcode>(make_shared_intercode(code));
            }
            return it->second;
        }
#else
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
#endif

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
