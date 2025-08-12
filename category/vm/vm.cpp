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

#include <category/core/assert.h>
#include <category/core/basic_formatter.hpp>
#include <category/core/keccak.hpp>
// #include <category/execution/ethereum/core/fmt/address_fmt.hpp>
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

#include <cstddef>
#include <cstdint>
#include <filesystem>
#include <iostream>
#include <memory>
#include <span>
#include <tbb/concurrent_hash_map.h>

namespace fs = std::filesystem;

namespace monad::vm
{
    using namespace monad::vm::utils;

    // Copied fmt::formatter for evmc::address from address_fmt.hpp to avoid
    // circular dependency.
    auto format_address(evmc::address const &value) {
        return fmt::format(
            "0x{:02x}",
            fmt::join(std::as_bytes(std::span(value.bytes)), ""));
    }

    typedef tbb::concurrent_hash_map<evmc::address, int, tbb::tbb_hash_compare<evmc::address>> ContractTable;
    typedef ContractTable::accessor Accessor;

    ContractTable call_counter;
    const int CONTRACT_CALL_THRESHOLD = 5;

    VM::VM(
        bool enable_async, std::size_t max_stack_cache,
        std::size_t max_memory_cache)
        : compiler_{enable_async}
        , stack_allocator_{max_stack_cache}
        , memory_allocator_{max_memory_cache}
    {
    }

    void log_contract(int64_t block_id, evmc_address const &code_address, evmc::bytes32 const &code_hash, SharedVarcode const& vcode) {
        ContractTable::accessor accessor;
        const auto itemIsNew = call_counter.insert(accessor, code_address);
        if (itemIsNew) {
            accessor->second = 1;
        }
        else {
            const int call_count = accessor->second;
            if (call_count != -1) {
                if (call_count > CONTRACT_CALL_THRESHOLD) {

                    // mark for insertion into the contracts dump
                    accessor->second = -1;
                    auto contracts_dir_var = std::getenv("CONTRACTS_DIR");
                    MONAD_ASSERT(contracts_dir_var);

                    // content addressable path for the contract using keccak of the actual code
                    auto const code_buf = vcode->intercode().get()->code();
                    auto const code_len = *(vcode->intercode().get()->code_size());

                    auto code_hash_dir = fs::path(contracts_dir_var) / "code_hash";
                    fs::create_directories(code_hash_dir);

                    auto contract_path = code_hash_dir / fmt::format("{}", intx::hex(intx::be::load<intx::uint256>(code_hash.bytes)));

                    auto os = std::ofstream(contract_path);
                    os.write(
                        reinterpret_cast<char const *>(code_buf),
                        static_cast<std::streamsize>(code_len));

                    auto block_prefix =
                        fmt::format("{}M", block_id / 1'000'000);

                    auto code_address_dir = fs::path(contracts_dir_var) / "code_address" / block_prefix /
                            fmt::format("{:02x}", code_address.bytes[0]) /
                            fmt::format("{:02x}", code_address.bytes[1]);

                    fs::create_directories(code_address_dir);

                    const evmc::address& addr = code_address;
                    auto contract_address_path = code_address_dir / format_address(addr);

                    fs::create_symlink(contract_path, contract_address_path);
                }
                else {
                    accessor->second = call_count + 1;
                }
            }
        }
        accessor.release();
    }

    template <Traits traits>
    evmc::Result VM::execute(
        Host &host, evmc_message const *msg, evmc::bytes32 const &code_hash,
        SharedVarcode const &vcode)
    {
        auto const *const host_itf = &host.get_interface();
        auto *const host_ctx = host.to_context();
        auto const &icode = vcode->intercode();
        auto rt_ctx = runtime::Context::from(
            memory_allocator_, host_itf, host_ctx, msg, icode->code_span());

        // Install new runtime context:
        auto *const prev_rt_ctx = host.set_runtime_context(&rt_ctx);

        auto result = execute_impl<traits>(rt_ctx, code_hash, vcode);

        // Re-install previous runtime context:
        (void)host.set_runtime_context(prev_rt_ctx);

        if (result.status_code == EVMC_SUCCESS) {
            log_contract(host.get_tx_context().block_number, msg->code_address, code_hash, vcode);
        }

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
        auto rt_ctx = runtime::Context::from(
            memory_allocator_, host_itf, host_ctx, msg, code);

        // Install new runtime context:
        auto *const prev_rt_ctx = host.set_runtime_context(&rt_ctx);

        auto result = execute_bytecode_impl<traits>(rt_ctx, code);

        // Re-install previous runtime context:
        (void)host.set_runtime_context(prev_rt_ctx);

        host.rethrow_on_active_exception();

        return result;
    }

    EXPLICIT_TRAITS_MEMBER(VM::execute_bytecode);

    template <Traits traits>
    evmc::Result VM::execute_raw(
        evmc_host_interface const *host, evmc_host_context *host_ctx,
        evmc_message const *msg, evmc::bytes32 const &code_hash,
        SharedVarcode const &vcode)
    {
        auto const &icode = vcode->intercode();
        auto rt_ctx = runtime::Context::from(
            memory_allocator_, host, host_ctx, msg, icode->code_span());
        return execute_impl<traits>(rt_ctx, code_hash, vcode);
    }

    EXPLICIT_TRAITS_MEMBER(VM::execute_raw);

    template <Traits traits>
    evmc::Result VM::execute_bytecode_raw(
        evmc_host_interface const *host, evmc_host_context *host_ctx,
        evmc_message const *msg, std::span<uint8_t const> code)
    {
        auto rt_ctx = runtime::Context::from(
            memory_allocator_, host, host_ctx, msg, code);
        return execute_bytecode_impl<traits>(rt_ctx, code);
    }

    EXPLICIT_TRAITS_MEMBER(VM::execute_bytecode_raw);

    template <Traits traits>
    evmc::Result VM::execute_intercode_raw(
        evmc_host_interface const *host, evmc_host_context *host_ctx,
        evmc_message const *msg, SharedIntercode const &icode)
    {
        auto rt_ctx = runtime::Context::from(
            memory_allocator_, host, host_ctx, msg, icode->code_span());
        return execute_intercode_impl<traits>(rt_ctx, icode);
    }

    EXPLICIT_TRAITS_MEMBER(VM::execute_intercode_raw);

    template <Traits traits>
    evmc::Result VM::execute_impl(
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
                return execute_intercode_impl<traits>(rt_ctx, icode);
            }
            auto const entry = ncode->entrypoint();
            if (MONAD_VM_UNLIKELY(entry == nullptr)) {
                // Compilation has failed in this revision, so just execute
                // with interpreter.
                return execute_intercode_impl<traits>(rt_ctx, icode);
            }
            // Bytecode has been successfully compiled for the right
            // revision.
            return execute_native_entrypoint_impl(rt_ctx, entry);
        }
        if (!compiler_.is_varcode_cache_warm()) {
            // If cache is not warm then start async compilation
            // immediately, and execute with interpreter in the meantime.
            compiler_.async_compile<traits>(code_hash, icode, compiler_config_);
            return execute_intercode_impl<traits>(rt_ctx, icode);
        }
        // Execute with interpreter. We will start async compilation when
        // the accumulated execution gas spent by interpreter on the
        // bytecode becomes sufficiently high.
        auto result = execute_intercode_impl<traits>(rt_ctx, icode);
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

    EXPLICIT_TRAITS_MEMBER(VM::execute_impl);

    template <Traits traits>
    evmc::Result VM::execute_bytecode_impl(
        runtime::Context &rt_ctx, std::span<uint8_t const> code)
    {
        stats_.event_execute_bytecode();

        auto const stack_ptr = stack_allocator_.allocate();
        interpreter::execute<traits>(rt_ctx, Intercode{code}, stack_ptr.get());

        return rt_ctx.copy_to_evmc_result();
    }

    EXPLICIT_TRAITS_MEMBER(VM::execute_bytecode_impl);

    template <Traits traits>
    evmc::Result VM::execute_intercode_impl(
        runtime::Context &rt_ctx, SharedIntercode const &icode)
    {
        stats_.event_execute_intercode();

        auto const stack_ptr = stack_allocator_.allocate();
        interpreter::execute<traits>(rt_ctx, *icode, stack_ptr.get());

        return rt_ctx.copy_to_evmc_result();
    }

    EXPLICIT_TRAITS_MEMBER(VM::execute_intercode_impl);

    evmc::Result VM::execute_native_entrypoint_raw(
        evmc_host_interface const *host, evmc_host_context *host_ctx,
        evmc_message const *msg, SharedIntercode const &icode,
        compiler::native::entrypoint_t entry)
    {
        auto rt_ctx = runtime::Context::from(
            memory_allocator_, host, host_ctx, msg, icode->code_span());
        return execute_native_entrypoint_impl(rt_ctx, entry);
    }

    evmc::Result VM::execute_native_entrypoint_impl(
        runtime::Context &rt_ctx, compiler::native::entrypoint_t entry)
    {
        stats_.event_execute_native_entrypoint();

        auto const stack_ptr = stack_allocator_.allocate();
        entry(&rt_ctx, stack_ptr.get());

        return rt_ctx.copy_to_evmc_result();
    }
}
