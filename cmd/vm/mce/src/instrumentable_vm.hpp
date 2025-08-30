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

#include <category/vm/compiler/ir/x86.hpp>
#include <category/vm/core/assert.h>
#include <category/vm/evm/chain.hpp>
#include <category/vm/runtime/allocator.hpp>

#include <asmjit/x86.h>
#include <evmc/evmc.h>
#include <evmc/evmc.hpp>
#include <evmone/evmone.h>
#include <valgrind/cachegrind.h>

#include "host.hpp"
#include "state.hpp"
#include "test_state.hpp"

#include <cstdint>
#include <iostream>
#include <vector>

using namespace monad;
using namespace monad::vm::compiler;
using namespace evmc::literals;

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
    monad::vm::runtime::EvmMemoryAllocator memory_allocator;

public:
    InstrumentableVM(asmjit::JitRuntime &rt)
        : evmc_vm{EVMC_ABI_VERSION, "monad-compiler-x86-microbenchmark-engine", "0.0.0", abi_compat::destroy, abi_compat::execute, abi_compat::get_capabilities, nullptr}
        , rt_(rt)
    {
    }

    template <monad::Traits traits>
    evmc::Result
    execute(native::entrypoint_t entry, InstrumentationDevice const device)
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
    evmc::Result execute(native::entrypoint_t entry)
    {
        MONAD_VM_ASSERT(entry != nullptr);
        using namespace evmone::state;

        auto msg = new evmc_message{
            .kind = EVMC_CALL,
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
            .code = nullptr,
            .code_size = 0,
        };

        auto vm = evmc::VM(this);

        auto const init_state = evmone::test::TestState{};
        auto evm_state = State{init_state};
        auto block = BlockInfo{};
        auto hashes = evmone::test::TestBlockHashes{};
        auto tx = Transaction{};

        auto host = Host(traits::evm_rev(), vm, evm_state, block, hashes, tx);

        auto const *interface = &host.get_interface();
        auto *context = host.to_context();

        std::vector<uint8_t> empty_code{};
        auto code_span = std::span<uint8_t const>{empty_code.data(), 0};

        auto ctx = vm::runtime::Context::from(
            memory_allocator,
            {.max_initcode_size = 0xC000},
            interface,
            context,
            msg,
            code_span);

        auto stack_ptr = stack_allocator.allocate();

        if constexpr (instrument) {
            if constexpr (device == InstrumentationDevice::Cachegrind) {
                CACHEGRIND_START_INSTRUMENTATION;
                entry(&ctx, stack_ptr.get());
                CACHEGRIND_STOP_INSTRUMENTATION;
            }
            else {
                timer.start();
                entry(&ctx, stack_ptr.get());
                timer.pause();
            }
        }
        else {
            entry(&ctx, stack_ptr.get());
        }

        delete msg;

        return ctx.copy_to_evmc_result();
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
