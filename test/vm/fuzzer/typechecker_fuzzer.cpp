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

#include <category/vm/compiler/ir/basic_blocks.hpp>
#include <category/vm/compiler/ir/local_stacks.hpp>
#include <category/vm/compiler/ir/poly_typed.hpp>
#include <category/vm/fuzzing/generator/choice.hpp>
#include <category/vm/fuzzing/generator/generator.hpp>
#include <category/vm/utils/debug.hpp>

#include <evmc/evmc.h>
#include <evmc/evmc.hpp>

#include <CLI/CLI.hpp>

#include <bits/chrono.h>
#include <cassert>
#include <chrono>
#include <cmath>
#include <cstddef>
#include <cstdint>
#include <cstdlib>
#include <format>
#include <iostream>
#include <limits>
#include <map>
#include <random>
#include <span>
#include <utility>
#include <vector>

using namespace monad;
using namespace monad::vm::fuzzing;
using namespace monad::vm::compiler;
using namespace monad::vm::interpreter;

using random_engine_t = std::mt19937_64;

namespace
{
    struct arguments
    {
        using seed_t = random_engine_t::result_type;
        static constexpr seed_t default_seed =
            std::numeric_limits<seed_t>::max();

        std::int64_t iterations_per_run = 100;
        seed_t seed = default_seed;
        std::size_t runs = std::numeric_limits<std::size_t>::max();
        evmc_revision revision = EVMC_CANCUN;

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
        "--seed",
        args.seed,
        "Seed to use for reproducible fuzzing (random by default)");

    app.add_option(
        "-r,--runs", args.runs, "Number of runs (unbounded by default)");

    auto const rev_map = std::map<std::string, evmc_revision>{
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

static void
fuzz_iteration(std::vector<uint8_t> const &contract, evmc_revision const)
{
    MONAD_VM_ASSERT(contract.size() <= *code_size_t::max());
    basic_blocks::BasicBlocksIR const ir2 =
        basic_blocks::BasicBlocksIR::unsafe_from(contract);
    local_stacks::LocalStacksIR ir3{ir2};
    poly_typed::PolyTypedIR ir{std::move(ir3)};

    ir.type_check_or_throw();
}

static void
log(std::chrono::high_resolution_clock::time_point start, arguments const &args,
    std::size_t const run_index)
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
}

// Coin toss, biased whenever p != 0.5
template <typename Engine>
static bool toss(Engine &engine, double p)
{
    std::bernoulli_distribution dist(p);
    return dist(engine);
}

static void do_run(std::size_t const run_index, arguments const &args)
{
    auto const rev = args.revision;

    auto engine = random_engine_t(args.seed);

    auto start_time = std::chrono::high_resolution_clock::now();

    for (auto i = 0; i < args.iterations_per_run; ++i) {
        using monad::vm::fuzzing::GeneratorFocus;
        auto focus = discrete_choice<GeneratorFocus>(
            engine,
            [](auto &) { return generic_focus; },
            Choice(0.05, [](auto &) { return pow2_focus; }),
            Choice(0.8, [](auto &) { return dyn_jump_focus; }));

        auto const contract =
            monad::vm::fuzzing::generate_program(focus, engine, rev, {});

        fuzz_iteration(contract, rev);
    }

    log(start_time, args, run_index);
}

static void run_loop(int argc, char **argv)
{
    auto args = parse_args(argc, argv);
    auto const *msg_rev = evmc_revision_to_string(args.revision);
    for (auto i = 0u; i < args.runs; ++i) {
        std::cerr << std::format(
            "Fuzzing with seed @ {}: {}\n", msg_rev, args.seed);
        do_run(i, args);
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
