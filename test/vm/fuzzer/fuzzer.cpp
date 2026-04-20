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

#include "assertions.hpp"
#include "compiler_hook.hpp"
#include "evmone_backend.hpp"
#include "fuzzer_backend.hpp"
#include "test_vm.hpp"

#include <category/vm/compiler/ir/x86/types.hpp>
#include <category/vm/evm/opcodes.hpp>
#include <category/vm/fuzzing/generator/choice.hpp>
#include <category/vm/fuzzing/generator/generator.hpp>
#include <category/vm/memory_pool.hpp>
#include <category/vm/utils/debug.hpp>

#include <evmone/evmone.h>

#include <evmc/evmc.h>
#include <evmc/evmc.hpp>

#include <CLI/CLI.hpp>

#include <algorithm>
#include <chrono>
#include <cstddef>
#include <cstdint>
#include <cstdlib>
#include <format>
#include <iostream>
#include <limits>
#include <map>
#include <optional>
#include <random>
#include <string>
#include <string_view>
#include <unordered_map>
#include <vector>

using namespace monad;
using namespace monad::vm::fuzzing;
using namespace std::chrono_literals;

using enum monad::vm::compiler::EvmOpCode;

static constexpr std::string_view to_string(evmc_status_code const sc) noexcept
{
    switch (sc) {
    case EVMC_SUCCESS:
        return "SUCCESS";
    case EVMC_FAILURE:
        return "FAILURE";
    case EVMC_REVERT:
        return "REVERT";
    case EVMC_OUT_OF_GAS:
        return "OUT_OF_GAS";
    case EVMC_INVALID_INSTRUCTION:
        return "INVALID_INSTRUCTION";
    case EVMC_UNDEFINED_INSTRUCTION:
        return "UNDEFINED_INSTRUCTION";
    case EVMC_STACK_OVERFLOW:
        return "STACK_OVERFLOW";
    case EVMC_STACK_UNDERFLOW:
        return "STACK_UNDERFLOW";
    case EVMC_BAD_JUMP_DESTINATION:
        return "BAD_JUMP_DESTINATION";
    case EVMC_INVALID_MEMORY_ACCESS:
        return "INVALID_MEMORY_ACCESS";
    case EVMC_CALL_DEPTH_EXCEEDED:
        return "CALL_DEPTH_EXCEEDED";
    case EVMC_STATIC_MODE_VIOLATION:
        return "STATIC_MODE_VIOLATION";
    case EVMC_PRECOMPILE_FAILURE:
        return "PRECOMPILE_FAILURE";
    case EVMC_ARGUMENT_OUT_OF_RANGE:
        return "ARGUMENT_OUT_OF_RANGE";
    case EVMC_INSUFFICIENT_BALANCE:
        return "INSUFFICIENT_BALANCE";
    case EVMC_INTERNAL_ERROR:
        return "INTERNAL_ERROR";
    case EVMC_REJECTED:
        return "REJECTED";
    case EVMC_OUT_OF_MEMORY:
        return "OUT_OF_MEMORY";
    default:
        return "OTHER";
    }
}

using random_engine_t = std::mt19937_64;

namespace
{
    struct arguments
    {
        using seed_t = random_engine_t::result_type;
        static constexpr seed_t default_seed =
            std::numeric_limits<seed_t>::max();

        std::int64_t iterations_per_run = 100;
        std::size_t messages = 4;
        seed_t seed = default_seed;
        std::size_t runs = std::numeric_limits<std::size_t>::max();
        bool print_stats = false;
        BlockchainTestVM::Implementation implementation =
            BlockchainTestVM::Implementation::Compiler;
        evmc_revision revision = EVMC_OSAKA;
        std::optional<std::string> focus_path = std::nullopt;
        std::optional<GeneratorFocus> focus = std::nullopt;

        void set_random_seed_if_default()
        {
            if (seed == default_seed) {
                seed = std::random_device()();
            }
        }
    };
}

static arguments parse_args(int const argc, char **const argv)
{
    auto app = CLI::App("Monad VM Fuzzer");
    auto args = arguments{};

    app.add_option(
        "-i,--iterations-per-run",
        args.iterations_per_run,
        "Number of fuzz iterations in each run (default 100)");

    app.add_option(
        "-n,--messages",
        args.messages,
        "Number of messages to send per iteration (default 4)");

    app.add_option(
        "--seed",
        args.seed,
        "Seed to use for reproducible fuzzing (random by default)");

    app.add_option("--focus", args.focus_path, "Path to the JSON focus config");

    auto const impl_map =
        std::map<std::string, BlockchainTestVM::Implementation>{
            {"interpreter", BlockchainTestVM::Implementation::Interpreter},
            {"compiler", BlockchainTestVM::Implementation::Compiler},
        };

    app.add_option(
           "--implementation", args.implementation, "VM implementation to fuzz")
        ->transform(CLI::CheckedTransformer(impl_map, CLI::ignore_case));

    app.add_option(
        "-r,--runs",
        args.runs,
        "Number of runs (evm state is reset between runs) (unbounded by "
        "default)");

    app.add_flag(
        "--print-stats",
        args.print_stats,
        "Print message result statistics when logging");

    auto const rev_map = std::map<std::string, evmc_revision>{
        {"HOMESTEAD", EVMC_HOMESTEAD},
        {"TANGERINE_WHISTLE", EVMC_TANGERINE_WHISTLE},
        {"TANGERINE WHISTLE", EVMC_TANGERINE_WHISTLE},
        {"SPURIOUS_DRAGON", EVMC_SPURIOUS_DRAGON},
        {"SPURIOUS DRAGON", EVMC_SPURIOUS_DRAGON},
        {"BYZANTIUM", EVMC_BYZANTIUM},
        {"CONSTANTINOPLE", EVMC_CONSTANTINOPLE},
        {"PETERSBURG", EVMC_PETERSBURG},
        {"ISTANBUL", EVMC_ISTANBUL},
        {"BERLIN", EVMC_BERLIN},
        {"LONDON", EVMC_LONDON},
        {"PARIS", EVMC_PARIS},
        {"SHANGHAI", EVMC_SHANGHAI},
        {"CANCUN", EVMC_CANCUN},
        {"PRAGUE", EVMC_PRAGUE},
        {"OSAKA", EVMC_OSAKA},
        {"LATEST", EVMC_LATEST_STABLE_REVISION}};
    app.add_option(
           "--revision",
           args.revision,
           std::format(
               "Set EVM revision (default: {})",
               evmc_revision_to_string(args.revision)))
        ->transform(CLI::CheckedTransformer(rev_map, CLI::ignore_case))
        ->option_text("TEXT");

    try {
        app.parse(argc, argv);
    }
    catch (CLI::ParseError const &e) {
        std::exit(app.exit(e));
    }

    args.set_random_seed_if_default();
    return args;
}

static evmc_status_code fuzz_iteration(
    evmc_message const &msg, evmc_revision const rev, FuzzerBackend &reference,
    FuzzerBackend &subject, bool const strict_out_of_gas)
{
    reference.ensure_exists(msg.sender);
    reference.ensure_exists(msg.recipient);
    subject.ensure_exists(msg.sender);
    subject.ensure_exists(msg.recipient);

    auto const ref_cp = reference.checkpoint();
    auto const ref_result = reference.execute(msg, rev);

    auto const sub_cp = subject.checkpoint();
    auto const sub_result = subject.execute(msg, rev);

    assert_equal(ref_result, sub_result, strict_out_of_gas);

    if (ref_result.status_code != EVMC_SUCCESS) {
        reference.rollback(ref_cp);
    }
    reference.normalize();

    if (sub_result.status_code != EVMC_SUCCESS) {
        subject.rollback(sub_cp);
    }
    subject.normalize();

    assert_backend_states_equal(reference, subject);
    return ref_result.status_code;
}

static void
log(std::chrono::high_resolution_clock::time_point start, arguments const &args,
    std::unordered_map<evmc_status_code, std::size_t> const &exit_code_stats,
    std::size_t const run_index, std::size_t const total_messages)
{
    using namespace std::chrono;

    constexpr auto ns_factor = duration_cast<nanoseconds>(1s).count();

    auto const end = high_resolution_clock::now();
    auto const diff = (end - start).count();
    auto const per_contract = diff / args.iterations_per_run;

    std::cerr << std::format(
        "[{}]: {:.4f}s / iteration\n",
        run_index + 1,
        static_cast<double>(per_contract) / ns_factor);

    if (args.print_stats) {
        for (auto const &[k, v] : exit_code_stats) {
            auto const percentage =
                (static_cast<double>(v) / static_cast<double>(total_messages)) *
                100;
            std::cerr << std::format(
                "  {:<21}: {:.2f}%\n", to_string(k), percentage);
        }
    }
}

template <typename Engine>
static evmc::VM create_monad_vm(arguments const &args, Engine &engine)
{
    using enum BlockchainTestVM::Implementation;

    monad::vm::compiler::native::EmitterHook hook = nullptr;

    if (args.implementation == Compiler) {
        hook = compiler_emit_hook(engine);
    }

    return evmc::VM(new BlockchainTestVM(args.implementation, hook));
}

// Coin toss, biased whenever p != 0.5
template <typename Engine>
static bool toss(Engine &engine, double p)
{
    std::bernoulli_distribution dist(p); // NOLINT(misc-const-correctness)
    return dist(engine);
}

static void do_run(
    monad::vm::MemoryPool &memory_pool, std::size_t const run_index,
    arguments const &args)
{
    auto const rev = args.revision;

    auto engine = random_engine_t(args.seed);

    constexpr GenesisAccount genesis[] = {genesis_account};
    auto reference = EvmoneBackend(evmc::VM(evmc_create_evmone()), genesis);
    auto subject = EvmoneBackend(create_monad_vm(args, engine), genesis);

    auto const max_code =
        std::min(reference.max_code_size(), subject.max_code_size());
    auto const strict_out_of_gas =
        args.implementation == BlockchainTestVM::Implementation::Interpreter;

    auto contract_addresses = std::vector<evmc::address>{};
    auto known_addresses = std::vector<evmc::address>{};

    auto exit_code_stats = std::unordered_map<evmc_status_code, std::size_t>{};
    auto total_messages = std::size_t{0};

    auto const start_time = std::chrono::high_resolution_clock::now();

    for (auto i = 0; i < args.iterations_per_run; ++i) {
        using monad::vm::fuzzing::GeneratorFocus;
        auto const &focus =
            args.focus
                ? *args.focus
                : discrete_choice<GeneratorFocus>(
                      engine,
                      [](auto &) { return generic_focus; },
                      Choice(0.60, [](auto &) { return pow2_focus; }),
                      Choice(0.05, [](auto &) { return dyn_jump_focus; }));

        if (rev >= EVMC_PRAGUE && toss(engine, 0.001)) {
            auto const precompile =
                monad::vm::fuzzing::generate_precompile_address(engine, rev);
            auto const a =
                reference.deploy_delegated(genesis_address, precompile);
            auto const b =
                subject.deploy_delegated(genesis_address, precompile);
            MONAD_ASSERT(a == b);
            assert_backend_states_equal(reference, subject);
            known_addresses.push_back(a);
        }

        for (;;) {
            auto const contract = monad::vm::fuzzing::generate_program(
                focus, engine, rev, known_addresses);

            if (contract.size() > max_code) {
                // It rarely happens that we generate contracts this large.
                std::cerr << "Skipping contract of size: " << contract.size()
                          << " bytes" << std::endl;
                continue;
            }

            auto const a = reference.deploy(genesis_address, contract);
            auto const b = subject.deploy(genesis_address, contract);
            MONAD_ASSERT(a == b);

            assert_backend_states_equal(reference, subject);

            contract_addresses.push_back(a);
            known_addresses.push_back(a);

            if (args.revision >= EVMC_PRAGUE && toss(engine, 0.2)) {
                auto const c = reference.deploy_delegated(genesis_address, a);
                auto const d = subject.deploy_delegated(genesis_address, a);
                MONAD_ASSERT(c == d);
                assert_backend_states_equal(reference, subject);
                known_addresses.push_back(c);
            }
            break;
        }

        for (auto j = 0u; j < args.messages; ++j) {
            auto msg_memory = memory_pool.alloc_ref();
            auto const msg = monad::vm::fuzzing::generate_message(
                focus,
                engine,
                contract_addresses,
                {genesis_address},
                [&](auto const &address) {
                    return reference.get_code(address);
                },
                msg_memory.get(),
                memory_pool.alloc_capacity());
            ++total_messages;

            auto const ec = fuzz_iteration(
                *msg, rev, reference, subject, strict_out_of_gas);
            ++exit_code_stats[ec];
        }
    }

    log(start_time, args, exit_code_stats, run_index, total_messages);
}

static void run_loop(int argc, char **argv)
{
    monad::vm::MemoryPool memory_pool{512};
    auto args = parse_args(argc, argv);
    if (args.focus_path) {
        args.focus = parse_generator_focus(*args.focus_path);
    }
    auto const *msg_rev = evmc_revision_to_string(args.revision);
    for (auto i = 0u; i < args.runs; ++i) {
        std::cerr << std::format(
            "Fuzzing with seed @ {}: {}\n", msg_rev, args.seed);
        do_run(memory_pool, i, args);
        args.seed = random_engine_t(args.seed)();
    }
}

int main(int argc, char **argv)
{
    if (monad::vm::utils::is_fuzzing_monad_vm) {
        run_loop(argc, argv);
        return 0;
    }
    std::cerr << "\nFuzzer not started:\n"
                 "Make sure to configure with -DMONAD_COMPILER_TESTING=ON and\n"
                 "set environment variable MONAD_COMPILER_FUZZING=1 before\n"
                 "starting the fuzzer\n";
    return 1;
}
