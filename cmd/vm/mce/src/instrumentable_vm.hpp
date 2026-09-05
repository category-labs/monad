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

#include <instrumentation_device.hpp>
#include <stopwatch.hpp>

#include <category/core/assert.h>
#include <category/core/log.hpp>
#include <category/execution/ethereum/chain/ethereum_mainnet.hpp>
#include <category/execution/ethereum/core/block.hpp>
#include <category/execution/ethereum/core/transaction.hpp>
#include <category/execution/ethereum/state2/block_state.hpp>
#include <category/execution/ethereum/state3/state.hpp>
#include <category/vm/compiler/ir/x86.hpp>
#include <category/vm/evm/message.hpp>
#include <category/vm/evm/traits.hpp>
#include <category/vm/memory_pool.hpp>
#include <category/vm/runtime/allocator.hpp>
#include <category/vm/vm.hpp>

#include <cmd/vm/mce/src/instrumentable_compiler.hpp>

#include <test/utils/test_state.hpp>
#include <test/vm/utils/test_block_hash_buffer.hpp>
#include <test/vm/utils/test_host.hpp>

#include <asmjit/x86.h>
#include <evmc/evmc.h>
#include <evmc/evmc.hpp>
#include <valgrind/cachegrind.h>

#include <cstdint>
#include <iostream>
#include <optional>
#include <vector>

using namespace monad;
using namespace monad::vm;
using namespace monad::vm::compiler;
using namespace monad::literals;
using namespace monad::vm::compiler::native;

namespace abi_compat
{
    // These are required for compatibility with the EVMC ABI. For now
    // they are either noops or aborts upon invocation. Later it would
    // be useful to support full interaction with the host.
    void destroy(evmc_vm *vm);

    evmc_result execute(
        evmc_vm *vm, evmc_host_interface const *host,
        evmc_host_context *context, evmc_revision rev, evmc_message const *msg,
        uint8_t const *code, size_t code_size);
    evmc_capabilities_flagset get_capabilities(evmc_vm *vm);
}

template <bool instrument>
class InstrumentableVM : public evmc_vm
{
    monad::vm::runtime::EvmStackAllocator stack_allocator;
    monad::vm::MemoryPool memory_pool_;
    monad::test::TestState<false> test_state_;
    monad::vm::VM vm_;

public:
    InstrumentableVM(asmjit::JitRuntime &rt)
        : evmc_vm{EVMC_ABI_VERSION, "monad-compiler-x86-microbenchmark-engine", "0.0.0", abi_compat::destroy, abi_compat::execute, abi_compat::get_capabilities, nullptr}
        , memory_pool_{8 * 1024 * 1024}
        , rt_(rt)
    {
    }

    template <monad::Traits traits>
    evmc::Result execute(Binary &entry, InstrumentationDevice const device)
    {
        switch (device) {
        case InstrumentationDevice::Cachegrind:
            return execute<traits, InstrumentationDevice::Cachegrind>(entry);
        case InstrumentationDevice::WallClock:
            return execute<traits, InstrumentationDevice::WallClock>(entry);
        }
        std::unreachable();
    }

    template <monad::Traits traits, InstrumentationDevice device>
    evmc::Result execute(Binary &entry)
    {
        auto msg_memory = memory_pool_.alloc_ref();
        auto msg = new monad_message{
            .kind = MONAD_CALL,
            .flags = 0,
            .depth = 0,
            .gas = 150'000'000,
            .recipient = {},
            .sender = {},
            .input_data = nullptr,
            .input_size = 0,
            .value = {},
            .create2_salt = {},
            .code_address = {},
            .memory_handle = msg_memory.get(),
            .memory = msg_memory.get(),
            .memory_capacity = memory_pool_.alloc_capacity(),
        };

        BlockState block_state{test_state_.trie_db, vm_};
        State state{block_state, Incarnation{0, 0}};
        state.push();
        for (auto const &addr : {msg->sender, msg->recipient}) {
            state.add_to_balance(addr, 0);
            state.access_account(addr);
        }

        monad::test::TestBlockHashBuffer const block_hash_buffer{};
        Transaction const tx{};
        BlockHeader const block_header{};
        EthereumMainnet const chain{};
        std::optional<uint256_t> const base_fee_per_gas{};
        std::vector<std::optional<Address>> const authorities{};

        monad::test::TestHost<traits> test_host{
            block_hash_buffer,
            state,
            tx,
            msg->sender,
            base_fee_per_gas,
            authorities,
            block_header,
            chain};
        auto &host = test_host.get_evmc_host();

        evmc_host_interface const *const interface = &host.get_interface();
        evmc_host_context *const context = host.to_context();

        std::vector<uint8_t> empty_code{};
        auto code_span = std::span<uint8_t const>{empty_code.data(), 0};

        auto ctx =
            vm::runtime::Context::from(interface, context, msg, code_span);

        auto stack_ptr = stack_allocator.allocate();

        if constexpr (instrument) {
            if constexpr (device == InstrumentationDevice::Cachegrind) {
                CACHEGRIND_START_INSTRUMENTATION;
                dispatch_execute(entry, &ctx, stack_ptr.get());
                CACHEGRIND_STOP_INSTRUMENTATION;
            }
            else {
                timer.start();
                dispatch_execute(entry, &ctx, stack_ptr.get());
                timer.pause();
            }
        }
        else {
            dispatch_execute(entry, &ctx, stack_ptr.get());
        }

        delete msg;

        return ctx.copy_to_evmc_result<traits>();
    }

    void dispatch_execute(
        Binary &entry, monad::vm::runtime::Context *ctx, uint8_t *stck)
    {
        entrypoint_t ep = entry.ncode->entrypoint();
        ep(ctx, stck);
    }

    evmc_capabilities_flagset get_capabilities() const
    {
        return EVMC_CAPABILITY_EVM1;
    }

private:
    asmjit::JitRuntime &rt_;
};

namespace abi_compat
{
    void destroy(evmc_vm *vm)
    {
        // The creator of the InstrumentableVM must destroy it.
        (void)vm;
    }

    evmc_result execute(
        evmc_vm *vm, evmc_host_interface const *host,
        evmc_host_context *context, evmc_revision rev, evmc_message const *msg,
        uint8_t const *code, size_t code_size)
    {
        // We don't support the host calling execute, yet...
        (void)vm;
        (void)host;
        (void)context;
        (void)rev;
        (void)msg;
        (void)code;
        (void)code_size;
        std::cout << "error: host -> native not yet implemented" << std::endl;
        abort();
    }

    evmc_capabilities_flagset get_capabilities(evmc_vm *vm)
    {
        (void)vm;
        return EVMC_CAPABILITY_EVM1;
    }

}
