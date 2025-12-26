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

#include <category/vm/code.hpp>
#include <category/vm/compiler/ir/x86.hpp>
#include <category/vm/compiler/ir/x86/types.hpp>
#include <category/vm/core/assert.h>
#include <category/vm/evm/explicit_traits.hpp>
#include <category/vm/evm/traits.hpp>
#include <category/vm/host.hpp>
#include <category/vm/runtime/allocator.hpp>
#include <category/vm/runtime/types.hpp>
#include <category/vm/vm.hpp>

#include <evmc/evmc.h>
#include <evmc/evmc.hpp>

#include <cstdint>
#include <memory>
#include <span>

namespace monad::vm
{
    using namespace monad::vm::utils;

    VM::VM(bool enable_async)
        : compiler_{enable_async}
        , stack_allocator_{}
        , memory_pool_{8 * 1024 * 1024}
    {
    }

    template <Traits traits>
    evmc::Result VM::execute(
        Host &host, evmc_message const *msg, evmc::bytes32 const &code_hash,
        SharedVarcode const &vcode)
    {
        auto const *const host_itf = &host.get_interface();
        auto *const host_ctx = host.to_context();
        auto const &icode = vcode->intercode();
        auto rt_ctx =
            runtime::Context::from(host_itf, host_ctx, msg, icode->code_span());

        // Install new runtime context:
        auto *const prev_rt_ctx = host.set_runtime_context(&rt_ctx);

        auto result = execute_raw<traits>(rt_ctx, code_hash, vcode);

        rt_ctx.return_to<traits>(prev_rt_ctx);

        // Re-install previous runtime context:
        (void)host.set_runtime_context(prev_rt_ctx);

        host.rethrow_on_active_exception();

        return result;
    }

    EXPLICIT_TRAITS_MEMBER(VM::execute);

    template <Traits traits>
    evmc::Result VM::execute_bytecode(
        Host &host, evmc_message const *msg, std::span<uint8_t const> code)
    {
        auto const *const host_itf = &host.get_interface();
        auto *const host_ctx = host.to_context();
        auto rt_ctx = runtime::Context::from(host_itf, host_ctx, msg, code);

        // Install new runtime context:
        auto *const prev_rt_ctx = host.set_runtime_context(&rt_ctx);

        auto result = execute_bytecode_raw<traits>(rt_ctx, code);

        rt_ctx.return_to<traits>(prev_rt_ctx);

        // Re-install previous runtime context:
        (void)host.set_runtime_context(prev_rt_ctx);

        host.rethrow_on_active_exception();

        return result;
    }

    EXPLICIT_TRAITS_MEMBER(VM::execute_bytecode);

    template <Traits traits>
    evmc::Result VM::execute_raw(
        runtime::Context &rt_ctx, evmc::bytes32 const &code_hash,
        SharedVarcode const &vcode)
    {
        auto const &icode = vcode->intercode();
        auto const &ncode = vcode->nativecode();
        auto const msg_gas = rt_ctx.gas_remaining;
        if (MONAD_VM_LIKELY(ncode != nullptr)) {
            // The bytecode is compiled.
            if (MONAD_VM_UNLIKELY(ncode->chain_id() != traits::id())) {
                // Revision change. The bytecode was compiled pre revision
                // change, so start async compilation immediately for the
                // new revision. Execute with interpreter in the meantime.
                compiler_.async_compile<traits>(
                    code_hash, icode, compiler_config_);
                return execute_intercode_raw<traits>(rt_ctx, icode);
            }
            auto const entry = ncode->entrypoint();
            if (MONAD_VM_UNLIKELY(entry == nullptr)) {
                // Compilation has failed in this revision, so just execute
                // with interpreter.
                return execute_intercode_raw<traits>(rt_ctx, icode);
            }
            // Bytecode has been successfully compiled for the right
            // revision.
            return execute_native_entrypoint_raw(rt_ctx, entry);
        }
        if (!compiler_.is_varcode_cache_warm()) {
            // If cache is not warm then start async compilation
            // immediately, and execute with interpreter in the meantime.
            compiler_.async_compile<traits>(code_hash, icode, compiler_config_);
            return execute_intercode_raw<traits>(rt_ctx, icode);
        }
        // Execute with interpreter. We will start async compilation when
        // the accumulated execution gas spent by interpreter on the
        // bytecode becomes sufficiently high.
        auto result = execute_intercode_raw<traits>(rt_ctx, icode);
        auto const bound = compiler::native::max_code_size(
            compiler_config_.max_code_size_offset, icode->code_size());
        MONAD_VM_DEBUG_ASSERT(result.gas_left >= 0);
        MONAD_VM_DEBUG_ASSERT(msg_gas >= result.gas_left);
        uint64_t const gas_used =
            static_cast<uint64_t>(msg_gas - result.gas_left);
        // Note that execution gas is counted for the second time via the
        // intercode_gas_used function if this is a re-execution.
        if (vcode->intercode_gas_used(gas_used) >= *bound) {
            compiler_.async_compile<traits>(code_hash, icode, compiler_config_);
        }
        return result;
    }

    EXPLICIT_TRAITS_MEMBER(VM::execute_raw);

    template <Traits traits>
    evmc::Result VM::execute_bytecode_raw(
        runtime::Context &rt_ctx, std::span<uint8_t const> code)
    {
        stats_.event_execute_bytecode();

        auto const stack_ptr = stack_allocator_.allocate();
        interpreter::execute<traits>(rt_ctx, Intercode{code}, stack_ptr.get());

        return rt_ctx.copy_to_evmc_result();
    }

    EXPLICIT_TRAITS_MEMBER(VM::execute_bytecode_raw);

    template <Traits traits>
    evmc::Result VM::execute_intercode_raw(
        runtime::Context &rt_ctx, SharedIntercode const &icode)
    {
        stats_.event_execute_intercode();

        auto const stack_ptr = stack_allocator_.allocate();
        interpreter::execute<traits>(rt_ctx, *icode, stack_ptr.get());

        return rt_ctx.copy_to_evmc_result();
    }

    EXPLICIT_TRAITS_MEMBER(VM::execute_intercode_raw);

    evmc::Result VM::execute_native_entrypoint_raw(
        runtime::Context &rt_ctx, compiler::native::entrypoint_t entry)
    {
        stats_.event_execute_native_entrypoint();

        auto const stack_ptr = stack_allocator_.allocate();
        entry(&rt_ctx, stack_ptr.get());

        return rt_ctx.copy_to_evmc_result();
    }
}
