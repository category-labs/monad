// This benchmark was adapted from the BurntPix Benchmark - EVM killer 2.0
// see: https://github.com/karalabe/burntpix-benchmark

#include "code_0a743ba7304efcc9e384ece9be7631e2470e401e.hpp"
#include "code_49206861766520746f6f206d7563682074696d65.hpp"
#include "code_c917e98213a05d271adc5d93d2fee6c1f1006f75.hpp"
#include "code_f529c70db0800449ebd81fbc6e4221523a989f05.hpp"
#include "code_snailtracer.hpp"
#include <test_vm.hpp>

#include "account.hpp"
#include "host.hpp"
#include "state.hpp"
#include "test_state.hpp"

#include <benchmark/benchmark.h>
#include <evmc/evmc.h>
#include <evmc/evmc.hpp>
#include <monad/vm/core/assert.h>

#include <cstdint>
#include <format>
#include <limits>

using namespace evmc::literals;
using namespace evmone::state;

using enum BlockchainTestVM::Implementation;

namespace
{
    static evmone::test::TestState burntpix_state()
    {
        evmone::test::TestState state;
        state[0x0a743ba7304efcc9e384ece9be7631e2470e401e_address] = {
            .nonce = 0,
            .balance = 0,
            .storage = {},
            .code = {
                code_0a743ba7304efcc9e384ece9be7631e2470e401e,
                code_0a743ba7304efcc9e384ece9be7631e2470e401e_len}};

        state[0x49206861766520746f6f206d7563682074696d65_address] = {
            .nonce = 0,
            .balance = 0,
            .storage = {},
            .code = {
                code_49206861766520746f6f206d7563682074696d65,
                code_49206861766520746f6f206d7563682074696d65_len}};

        auto &storage =
            state[0x49206861766520746f6f206d7563682074696d65_address].storage;
        storage[bytes32{0}] =
            0x000000000000000000000000f529c70db0800449ebd81fbc6e4221523a989f05_bytes32;
        storage[bytes32{1}] =
            0x0000000000000000000000000a743ba7304efcc9e384ece9be7631e2470e401e_bytes32;
        storage[bytes32{2}] =
            0x000000000000000000000000c917e98213a05d271adc5d93d2fee6c1f1006f75_bytes32;

        state[0xc917e98213a05d271adc5d93d2fee6c1f1006f75_address] = {
            .nonce = 0,
            .balance = 0,
            .storage = {},
            .code = {
                code_c917e98213a05d271adc5d93d2fee6c1f1006f75,
                code_c917e98213a05d271adc5d93d2fee6c1f1006f75_len}};

        state[0xf529c70db0800449ebd81fbc6e4221523a989f05_address] = {
            .nonce = 0,
            .balance = 0,
            .storage = {},
            .code = {
                code_f529c70db0800449ebd81fbc6e4221523a989f05,
                code_f529c70db0800449ebd81fbc6e4221523a989f05_len}};

        return state;
    }

    struct InputData
    {
        unsigned char func[4] = {0xa4, 0xde, 0x9a, 0xb4};
        bytes32 seed;
        bytes32 iterations;
    };

    void touch_init_state(
        evmone::test::TestState const &init_state, evmone::state::State &state)
    {
        for (auto const &[addr, _] : init_state) {
            state.find(addr);
        }
    };

    void run_burntpix(
        benchmark::State &state, BlockchainTestVM::Implementation const impl,
        uint64_t const seed, uint64_t const iterations)
    {
        auto vm = evmc::VM(new BlockchainTestVM(impl));
        auto *vm_ptr =
            reinterpret_cast<BlockchainTestVM *>(vm.get_raw_pointer());

        auto const burntpix_init_state = burntpix_state();
        vm_ptr->precompile_contracts(EVMC_CANCUN, burntpix_init_state);

        constexpr auto addr =
            0x49206861766520746f6f206d7563682074696d65_address;
        constexpr auto sender =
            0x49206861766520746f6f206d7563682074696f01_address;

        auto const code = burntpix_init_state.get_account_code(addr);

        InputData input_data{
            .seed = bytes32{seed}, .iterations = bytes32{iterations}};

        auto msg = evmc_message{
            .kind = EVMC_CALL,
            .flags = 0,
            .depth = 0,
            .gas = std::numeric_limits<int64_t>::max(),
            .recipient = addr,
            .sender = sender,
            .input_data = reinterpret_cast<uint8_t const *>(&input_data),
            .input_size = sizeof(InputData),
            .value = {},
            .create2_salt = {},
            .code_address = addr,
            .code = nullptr,
            .code_size = 0,
        };

        for (auto _ : state) {
            state.PauseTiming();
            auto evm_state = evmone::state::State{burntpix_init_state};
            touch_init_state(burntpix_init_state, evm_state);
            auto host = Host(
                EVMC_CANCUN,
                vm,
                evm_state,
                BlockInfo{},
                evmone::test::TestBlockHashes{},
                Transaction{});
            auto const *interface = &host.get_interface();
            auto *ctx = host.to_context();
            state.ResumeTiming();

            auto const result = evmc::Result{vm_ptr->execute(
                interface, ctx, EVMC_CANCUN, &msg, code.data(), code.size())};

            MONAD_VM_DEBUG_ASSERT(result.status_code == EVMC_SUCCESS);
        }
    }

    void register_burntpix(uint64_t seed, uint64_t iterations)
    {
        for (auto const impl : {Interpreter, Compiler, Evmone}) {
            benchmark::RegisterBenchmark(
                std::format(
                    "burntpix/{:#x}/{:#x}/{}",
                    seed,
                    iterations,
                    BlockchainTestVM::impl_name(impl)),
                run_burntpix,
                impl,
                seed,
                iterations);
        }
    }

    constexpr evmone::test::TestState snailtracer_state()
    {
        evmone::test::TestState state;

        state[0x49206861766520746f6f206d7563682074696d65_address] = {
            .nonce = 0,
            .balance = 0,
            .storage = {},
            .code = {code_snailtracer, code_snailtracer_len}};
        return state;
    }

    void run_snailtracer(
        benchmark::State &state, BlockchainTestVM::Implementation const impl)
    {
        auto vm = evmc::VM(new BlockchainTestVM(impl));
        auto *vm_ptr =
            reinterpret_cast<BlockchainTestVM *>(vm.get_raw_pointer());

        auto const snailtracer_init_state = snailtracer_state();
        auto intra_state = State{snailtracer_init_state};
        vm_ptr->precompile_contracts(EVMC_CANCUN, snailtracer_init_state);

        constexpr auto addr =
            0x49206861766520746f6f206d7563682074696d65_address;
        constexpr auto sender =
            0x49206861766520746f6f206d7563682074696f01_address;

        auto const code = intra_state.get_code(addr);

        uint8_t func[4] = {0x30, 0x62, 0x7b, 0x7c};

        auto msg = evmc_message{
            .kind = EVMC_CALL,
            .flags = 0,
            .depth = 0,
            .gas = std::numeric_limits<int64_t>::max(),
            .recipient = addr,
            .sender = sender,
            .input_data = reinterpret_cast<uint8_t const *>(&func),
            .input_size = 4,
            .value = {},
            .create2_salt = {},
            .code_address = addr,
            .code = nullptr,
            .code_size = 0,
        };

        for (auto _ : state) {
            state.PauseTiming();
            auto evm_state = State{snailtracer_init_state};
            touch_init_state(snailtracer_init_state, evm_state);
            auto host = Host(
                EVMC_CANCUN,
                vm,
                evm_state,
                BlockInfo{},
                evmone::test::TestBlockHashes{},
                Transaction{});
            auto const *interface = &host.get_interface();
            auto *ctx = host.to_context();
            state.ResumeTiming();

            auto const result = evmc::Result{vm_ptr->execute(
                interface, ctx, EVMC_CANCUN, &msg, code.data(), code.size())};

            MONAD_VM_DEBUG_ASSERT(result.status_code == EVMC_SUCCESS);
        }
    }
}

int main(int argc, char **argv)
{
    register_burntpix(0x0, 0x7A120);
    register_burntpix(0xD0FC9AE, 0x7A120);
    register_burntpix(0xF1FD58E, 0x7A120);
    register_burntpix(0x2456635E, 0x7A120);
    register_burntpix(0x25FAAB93, 0x7A120);
    register_burntpix(0x287FBB44, 0x7A120);
    register_burntpix(0x3F502349, 0x7A120);
    register_burntpix(0x58F5D174, 0x7A120);
    register_burntpix(0xBAB62971, 0x7A120);
    register_burntpix(0xCD3BAB83, 0x7A120);
    register_burntpix(0xD72C0032, 0x7A120);
    register_burntpix(0xFCC0C87B, 0x7A120);

    for (auto const impl : {Interpreter, Compiler, Evmone}) {
        benchmark::RegisterBenchmark(
            std::format("snailtracer/{}", BlockchainTestVM::impl_name(impl)),
            run_snailtracer,
            impl);
    }

    benchmark::Initialize(&argc, argv);
    benchmark::RunSpecifiedBenchmarks();
    benchmark::Shutdown();
    return 0;
}
