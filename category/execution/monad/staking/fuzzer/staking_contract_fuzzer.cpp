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

#include <category/execution/monad/staking/fuzzer/staking_contract_machine.hpp>
#include <category/execution/monad/staking/util/test_util.hpp>

#include <CLI/CLI.hpp>

#include <evmc/evmc.hpp>

using namespace monad;
using namespace monad::staking;
using namespace monad::staking::test;
using namespace evmc::literals;

static StakingContractMachine::Transition
gen_transition(StakingContractMachine &machine)
{
    auto const p = machine.gen() % 100;
    if (p < 30) {
        if (p < 20) {
            return StakingContractMachine::Transition::syscall_reward;
        }
        return StakingContractMachine::Transition::precompile_external_reward;
    }
    return machine.gen_transition();
}

static StakingContractMachine::seed_t
run_simulation(StakingContractMachine::seed_t seed, uint64_t depth)
{
    MONAD_ASSERT(depth > 0);

    std::cout << "Simulation with seed " << seed << std::endl;

    auto const start_time = std::chrono::steady_clock::now();

    StakingContractMachine machine{seed};
    double success_count = 0;
    for (size_t i = 0; i < depth; ++i) {
        if (machine.transition(gen_transition(machine))) {
            ++success_count;
        }
    }

    auto const end_time = std::chrono::steady_clock::now();

    auto const success_ratio = success_count / static_cast<double>(depth);
    auto const time =
        static_cast<double>((end_time - start_time).count()) / 1'000'000;

    std::cout << "    success ratio: " << success_ratio << '\n'
              << "  simulation time: " << time << " ms" << std::endl;

    return machine.gen();
}

namespace
{
    struct CommandArgs
    {
        StakingContractMachine::seed_t seed = 0;
        uint64_t depth = 100;
        uint64_t runs = std::numeric_limits<uint64_t>::max();
    };

    CommandArgs parse_args(int const argc, char **const argv)
    {
        auto app = CLI::App("Staking Contract Fuzzer");
        auto args = CommandArgs{};

        app.add_option(
            "--seed",
            args.seed,
            "Seed for reproducible fuzzing (0 by default)");

        app.add_option(
            "--depth",
            args.depth,
            "Staking contract transitions per simulation (default 100)");

        app.add_option(
            "--runs",
            args.runs,
            "Number of simulations to execute (default max uint64)");

        try {
            app.parse(argc, argv);
        }
        catch (CLI::ParseError const &e) {
            std::exit(app.exit(e));
        }

        return args;
    }
}

int main(int argc, char **argv)
{
    auto args = parse_args(argc, argv);

    std::cout << "Running " << args.runs << " simulations\n"
              << "  depth: " << args.depth << '\n'
              << "   seed: " << args.seed << std::endl;

    size_t seed = args.seed;
    for (size_t i = 0; i < args.runs; ++i) {
        seed = run_simulation(seed, args.depth);
    }
}
