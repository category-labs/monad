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
#include "block.hpp"
#include "compiler_hook.hpp"
#include "test_vm.hpp"

#include "account.hpp"
#include "hash_utils.hpp"
#include "host.hpp"
#include "state.hpp"
#include "test_state.hpp"
#include "transaction.hpp"

#include <category/vm/compiler/ir/basic_blocks.hpp>
#include <category/vm/compiler/ir/x86/types.hpp>
#include <category/vm/core/assert.h>
#include <category/vm/core/cases.hpp>
#include <category/vm/evm/opcodes.hpp>
#include <category/vm/fuzzing/generator/choice.hpp>
#include <category/vm/fuzzing/generator/generator.hpp>
#include <category/vm/fuzzing/generator/shrinker.hpp>
#include <category/vm/utils/debug.hpp>

#include <category/core/byte_string.hpp>
#include <category/execution/ethereum/core/fmt/address_fmt.hpp>

#include <evmone/constants.hpp>
#include <evmone/evmone.h>

#include <evmc/evmc.h>
#include <evmc/evmc.hpp>

#include <CLI/CLI.hpp>
#include <intx/intx.hpp>

#include <algorithm>
#include <array>
#include <bits/chrono.h>
#include <cassert>
#include <chrono>
#include <cmath>
#include <cstddef>
#include <cstdint>
#include <cstdlib>
#include <format>
#include <functional>
#include <iostream>
#include <limits>
#include <map>
#include <random>
#include <span>
#include <string_view>
#include <unordered_map>
#include <utility>
#include <vector>

using namespace evmone::state;
using namespace evmc::literals;
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

static constexpr auto genesis_address =
    0xBEEFCAFE000000000000000000000000BA5EBA11_address;

static constexpr auto block_gas_limit = 300'000'000;

static evmone::test::TestState initial_state()
{
    auto init = evmone::test::TestState{};
    // Genesis account with some large balance, but sufficiently small
    // so that token supply will not overflow uint256.
    init[genesis_address] = {
        .balance = std::numeric_limits<intx::uint256>::max() / 2,
        .storage = {},
        .code = {}};
    return init;
}

static Transaction tx_from(State &state, evmc::address const &addr) noexcept
{
    auto tx = Transaction{};
    tx.gas_limit = block_gas_limit;
    tx.sender = addr;
    tx.nonce = state.get_or_insert(addr).nonce;
    return tx;
}

// Derived from the evmone transition implementation; transaction-related
// book-keeping is elided here to keep the implementation simple and allow us to
// send arbitrary messages to update the state.
static evmc::Result transition(
    State &state, evmc_message const &msg, evmc_revision const rev,
    evmc::VM &vm, std::int64_t const block_gas_left)
{
    // Pre-transaction clean-up.
    // - Clear transient storage.
    // - Set accounts and their storage access status to cold.
    // - Clear the "just created" account flag.
    for (auto &[addr, acc] : state.get_modified_accounts()) {
        acc.transient_storage.clear();
        acc.access_status = EVMC_ACCESS_COLD;
        acc.just_created = false;
        for (auto &[key, val] : acc.storage) {
            val.access_status = EVMC_ACCESS_COLD;
            val.original = val.current;
        }
    }

    // TODO(BSC): fill out block and host context properly; should all work fine
    // for the moment as zero values from the perspective of the VM
    // implementations.
    auto block = BlockInfo{};
    auto hashes = evmone::test::TestBlockHashes{};
    auto tx = tx_from(state, msg.sender);
    tx.to = msg.recipient;

    constexpr auto effective_gas_price = 10;

    auto *sender_ptr = state.find(msg.sender);
    auto &sender_acc =
        (sender_ptr != nullptr) ? *sender_ptr : state.insert(msg.sender);

    ++sender_acc.nonce;
    sender_acc.balance -= block_gas_left * effective_gas_price;

    Host host{rev, vm, state, block, hashes, tx};

    sender_acc.access_status = EVMC_ACCESS_WARM; // Tx sender is always warm.
    if (tx.to.has_value()) {
        host.access_account(*tx.to);
    }

    auto result = host.call(msg);
    auto gas_used = block_gas_left - result.gas_left;

    auto const max_refund_quotient = rev >= EVMC_LONDON ? 5 : 2;
    auto const refund_limit = gas_used / max_refund_quotient;
    auto const refund = std::min(result.gas_refund, refund_limit);
    gas_used -= refund;

    sender_acc.balance += (block_gas_left - gas_used) * effective_gas_price;

    // Apply destructs.
    std::erase_if(
        state.get_modified_accounts(),
        [](std::pair<address const, Account> const &p) noexcept {
            return p.second.destructed;
        });

    // Delete empty accounts after every transaction. This is strictly required
    // until Byzantium where intermediate state root hashes are part of the
    // transaction receipt.
    // TODO: Consider limiting this only to Spurious Dragon.
    if (rev >= EVMC_SPURIOUS_DRAGON) {
        std::erase_if(
            state.get_modified_accounts(),
            [](std::pair<address const, Account> const &p) noexcept {
                auto const &acc = p.second;
                return acc.erase_if_empty && acc.is_empty();
            });
    }

    return result;
}

static void deploy_contract(
    State &state, evmc::address const &to,
    std::span<std::uint8_t const> const code_)
{
    auto code = bytes{code_.data(), code_.size()};

    FUZZER_ASSERT(state.find(to) == nullptr);

    state.insert(
        to,
        Account{
            .nonce = 0,
            .balance = 0,
            .code_hash = evmone::keccak256(code),
            .storage = {},
            .transient_storage = {},
            .code = code});

    FUZZER_ASSERT(state.find(to) != nullptr);
}

static void deploy_delegated_contract(
    State &state, evmc::address const &to, evmc::address const &delegatee)
{
    std::vector<uint8_t> code = {0xef, 0x01, 0x00};
    code.append_range(delegatee.bytes);
    FUZZER_ASSERT(code.size() == 23);
    deploy_contract(state, to, code);
}

static void deploy_contracts(
    State &evmone_state, State &monad_state, evmc::address const &to,
    std::span<std::uint8_t const> const code_)
{
    deploy_contract(evmone_state, to, code_);
    deploy_contract(monad_state, to, code_);
    assert_equal(evmone_state, monad_state);
}

static void deploy_delegated_contracts(
    State &evmone_state, State &monad_state, evmc::address const &to,
    evmc::address delegatee)
{
    deploy_delegated_contract(evmone_state, to, delegatee);
    deploy_delegated_contract(monad_state, to, delegatee);
    assert_equal(evmone_state, monad_state);
}

// It's possible for the compiler and evmone to reach equivalent-but-not-equal
// states after both executing. For example, the compiler may exit a block
// containing an SSTORE early because of unconditional underflow later in the
// block. Evmone will instead execute the SSTORE, then roll back the change.
// Because of how rollback is implemented, this produces a state with a mapping
// `K |-> 0` for some key `K`. This won't directly compare equal to the _empty_
// state that the compiler has, and so we need to normalise the states after
// execution to remove cold zero slots.
static void clean_storage(State &state)
{
    for (auto &[addr, acc] : state.get_modified_accounts()) {
        for (auto it = acc.storage.begin(); it != acc.storage.end();) {
            auto const &[k, v] = *it;

            if (v.current == evmc::bytes32{} && v.original == evmc::bytes32{} &&
                v.access_status == EVMC_ACCESS_COLD) {
                it = acc.storage.erase(it);
            }
            else {
                ++it;
            }
        }
        for (auto it = acc.transient_storage.begin();
             it != acc.transient_storage.end();) {
            auto const &[k, v] = *it;
            if (v == evmc::bytes32{}) {
                it = acc.transient_storage.erase(it);
            }
            else {
                ++it;
            }
        }
    }
}

using random_engine_t = std::mt19937_64;
using seed_t = random_engine_t::result_type;

namespace
{
    struct arguments
    {
        static constexpr seed_t default_seed =
            std::numeric_limits<seed_t>::max();

        std::int64_t iterations_per_run = 100;
        std::size_t messages = 4;
        seed_t seed = default_seed;
        std::size_t runs = std::numeric_limits<std::size_t>::max();
        bool print_stats = false;
        bool print_shrinker_state = false;
        BlockchainTestVM::Implementation implementation =
            BlockchainTestVM::Implementation::Compiler;
        evmc_revision revision = EVMC_OSAKA;
        std::optional<std::string> focus_path = std::nullopt;
        std::optional<GeneratorFocus> focus = std::nullopt;
        // Disable compiler hook introducing randomness in compilation
        bool deterministic_compilation = false;
        // When shrinking a contract, do not change the compiler hook seed
        bool shrink_contract_seed = false;
        std::size_t run_shrinking_attempts = 100;
        std::size_t contract_shrinking_attempts = 100;

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
#ifdef MONAD_COMPILER_LLVM
            {"llvm", BlockchainTestVM::Implementation::LLVM},
#endif
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

    app.add_flag(
        "--print-shrinker-state",
        args.print_shrinker_state,
        "Print size of run when shrinking");

    app.add_flag(
        "--deterministic-compilation",
        args.deterministic_compilation,
        "Enable deterministic compilation (no randomness)");

    app.add_flag(
        "--shrink-contract-seed",
        args.shrink_contract_seed,
        "Try with different the compiler hook seed when shrinking a contract");

    app.add_option(
        "--run-shrinking-attempts",
        args.run_shrinking_attempts,
        "Number of run shrinking attempts (default 100)");

    app.add_option(
        "--contract-shrinking-attempts",
        args.contract_shrinking_attempts,
        "Number of contract shrinking attempts (default 100)");

    auto const rev_map = std::map<std::string, evmc_revision>{
        {"FRONTIER", EVMC_FRONTIER},
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
    evmc_message const &msg, evmc_revision const rev, State &evmone_state,
    evmc::VM &evmone_vm, State &monad_state, evmc::VM &monad_vm,
    BlockchainTestVM::Implementation const impl)
{
    for (State &state : {std::ref(evmone_state), std::ref(monad_state)}) {
        state.get_or_insert(msg.sender);
        state.get_or_insert(msg.recipient);
    }

    auto const evmone_checkpoint = evmone_state.checkpoint();
    auto const evmone_result =
        transition(evmone_state, msg, rev, evmone_vm, block_gas_limit);

    auto const monad_checkpoint = monad_state.checkpoint();
    auto const monad_result =
        transition(monad_state, msg, rev, monad_vm, block_gas_limit);

    assert_equal(
        evmone_result,
        monad_result,
        impl == BlockchainTestVM::Implementation::Interpreter);

    if (evmone_result.status_code != EVMC_SUCCESS) {
        evmone_state.rollback(evmone_checkpoint);
    }
    clean_storage(evmone_state);

    if (monad_result.status_code != EVMC_SUCCESS) {
        monad_state.rollback(monad_checkpoint);
    }
    clean_storage(monad_state);

    assert_equal(evmone_state, monad_state);
    return evmone_result.status_code;
}

static void log_prepare(
    std::chrono::high_resolution_clock::time_point start,
    std::size_t const run_index, std::size_t const run_size)
{
    using namespace std::chrono;

    constexpr auto ns_factor = duration_cast<nanoseconds>(1s).count();

    auto const end = high_resolution_clock::now();
    auto const diff = (end - start).count();
    auto const per_contract = diff / static_cast<int64_t>(run_size);

    std::cerr << std::format(
        "[{}]: {:.4f}s / iteration (prepare)\n",
        run_index + 1,
        static_cast<double>(per_contract) / ns_factor);
}

static void log_run(
    std::chrono::high_resolution_clock::time_point start, arguments const &args,
    std::unordered_map<evmc_status_code, std::size_t> const &exit_code_stats,
    std::size_t const run_index, std::size_t const iteration_count,
    std::size_t const total_messages)
{
    using namespace std::chrono;

    constexpr auto ns_factor = duration_cast<nanoseconds>(1s).count();

    auto const end = high_resolution_clock::now();
    auto const diff = (end - start).count();
    auto const per_contract = diff / static_cast<int64_t>(iteration_count);

    std::cerr << std::format(
        "[{}]: {:.4f}s / iteration (run)\n",
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
static evmc::VM create_monad_vm(
    arguments const &args, Engine &engine,
    std::unordered_map<evmc::address, seed_t> const &hook_seed_map)
{
    using enum BlockchainTestVM::Implementation;

    monad::vm::compiler::native::EmitterHook hook = nullptr;
    std::function<void(evmc_message const *msg)> execute_hook = nullptr;

    // The compiler hook introduces non-determinism in the compilation process
    // that must be controlled for the fuzzer to be effective. To do so, we
    // assign each contract a seed, and reset the hook's RNG using that seed
    // before each compilation so that the hook has the same influence each time
    // that contract is compiled.
    //
    // This ensures that the shrinker can reliably reproduce the same
    // compilation result for a given contract as it removes steps from the run,
    // making the shrinking predicate deterministic when removing contracts.
    //
    // When shrinking individual contracts, removing instructions can shift the
    // state of the hook RNG such that instructions following the removed
    // instructions are compiled differently. This can lead to false negatives,
    // where the shrinker thinks the smaller input does not reproduce the
    // failure, when in fact it would if the hook RNG state was the same.
    //
    // This could be solved by assigning a seed per instruction, but that would
    // require a more complex mechanism to track and reset the RNG state, as
    // well as pregenerating even more values that would slow down the fuzzer in
    // the non-shrinking case, which we want to avoid.
    //
    // Fortunately, most counter-examples found by the fuzzer involve only a few
    // contracts, meaning that problem can be mitigated by increasing the number
    // of shrinking attempts, effectively sampling the shrinking predicate
    // multiple times.
    if (args.implementation == Compiler && !args.deterministic_compilation) {

        // FIXME: This is not thread-safe, but the fuzzer is single-threaded.
        static Engine hook_engine = random_engine_t(0);

        execute_hook = [&hook_seed_map](evmc_message const *msg) {
            auto const seed_it = hook_seed_map.find(msg->recipient);
            if (seed_it == hook_seed_map.end()) {
                hook_engine = random_engine_t(0);
            }
            else {
                auto const seed = seed_it->second;
                hook_engine = random_engine_t(seed);
            }
        };

        hook = compiler_emit_hook(engine, &hook_engine);
    }

    return evmc::VM(
        new BlockchainTestVM(args.implementation, hook, execute_hook));
}

struct DeployContract
{
    seed_t contract_hook_seed;
    evmc::address contract_address;
    std::vector<BasicBlock> contract;
};

struct DeployPrecompile
{
    evmc::address contract_address;
    evmc::address precompile_address;
};

struct DeployDelegatedContract
{
    evmc::address contract_address;
    evmc::address delegatee_address;
};

struct SendMessage
{
    evmc_message message;
};

// A run is a sequence of contract deployments and messages to send.
using RunStep = std::variant<
    DeployContract, DeployPrecompile, DeployDelegatedContract, SendMessage>;

using Run = std::vector<RunStep>;

static evmc::address prepare_address(evmc::address const &from, uint64_t &nonce)
{
    return compute_create_address(from, nonce++);
}

// An iteration consists of the following steps:
// 1. Optionally deploying a precompile contract
// 2. Deploying a contract
// 3. Optionally deploying a delegated contract
// 4. Sending a few messages to deployed contracts
template <typename Engine>
static void prepare_iteration(
    arguments const &args, Engine &engine, Run &run,
    std::vector<evmc::address> &known_addresses,
    std::vector<evmc::address> &contract_addresses,
    std::unordered_map<address, std::vector<std::uint8_t>> &contract_codes,
    uint64_t &nonce)
{
    auto const rev = args.revision;

    using monad::vm::fuzzing::GeneratorFocus;
    auto const &focus =
        args.focus ? *args.focus
                   : discrete_choice<GeneratorFocus>(
                         engine,
                         [](auto &) { return generic_focus; },
                         Choice(0.60, [](auto &) { return pow2_focus; }),
                         Choice(0.05, [](auto &) { return dyn_jump_focus; }));

    if (rev >= EVMC_PRAGUE && toss(engine, 0.001)) {
        auto precompile_address =
            monad::vm::fuzzing::generate_precompile_address(engine, rev);
        auto const contract_address = prepare_address(genesis_address, nonce);
        known_addresses.push_back(contract_address);
        run.push_back(DeployPrecompile{contract_address, precompile_address});
    }

    for (;;) {
        std::vector<BasicBlock> contract =
            monad::vm::fuzzing::generate_basic_blocks(
                focus, engine, rev, known_addresses);

        auto const compiled_contract = compile_program(contract);
        if (compiled_contract.size() > evmone::MAX_CODE_SIZE) {
            // The evmone host will fail when we attempt to deploy
            // contracts of this size. It rarely happens that we
            // generate contract this large.
            std::cerr << "Skipping contract of size: "
                      << compiled_contract.size() << " bytes" << std::endl;
            continue;
        }

        auto const contract_seed = engine();
        auto const contract_address = prepare_address(genesis_address, nonce);

        known_addresses.push_back(contract_address);
        contract_addresses.push_back(contract_address);
        contract_codes[contract_address] = compiled_contract;
        run.push_back(
            DeployContract{contract_seed, contract_address, contract});

        if (args.revision >= EVMC_PRAGUE && toss(engine, 0.2)) {
            auto const delegated_contract_address =
                prepare_address(genesis_address, nonce);
            known_addresses.push_back(delegated_contract_address);
            run.push_back(DeployDelegatedContract{
                delegated_contract_address, contract_address});
        }
        break;
    }

    for (auto j = 0u; j < args.messages; ++j) {
        auto msg = monad::vm::fuzzing::generate_message(
            focus,
            engine,
            contract_addresses,
            {genesis_address},
            [&](auto const &address) {
                if (auto it = contract_codes.find(address);
                    it != contract_codes.end()) {
                    return bytes{it->second.data(), it->second.size()};
                }
                return evmc::bytes{};
            });
        run.push_back(SendMessage{msg});
    }
}

static Run prepare_run(arguments const &args)
{
    auto engine = random_engine_t(args.seed);
    auto run = std::vector<RunStep>{};
    auto contract_addresses = std::vector<evmc::address>{};
    auto known_addresses = std::vector<evmc::address>{};
    std::unordered_map<address, std::vector<std::uint8_t>> contract_codes;
    uint64_t nonce = 0;
    for (auto i = 0; i < args.iterations_per_run; ++i) {
        prepare_iteration(
            args,
            engine,
            run,
            known_addresses,
            contract_addresses,
            contract_codes,
            nonce);
    }
    return run;
}

static void do_run(
    std::size_t const run_index, arguments const &args, bool const verbose,
    Run const &run, size_t &iteration_index)
{
    auto const rev = args.revision;

    auto engine = random_engine_t(args.seed);

    auto evmone_vm = evmc::VM(evmc_create_evmone());
    auto compiler_hook_seed_map = std::unordered_map<evmc::address, seed_t>{};
    for (auto const &step : run) {
        if (std::holds_alternative<DeployContract>(step)) {
            auto const &d = std::get<DeployContract>(step);
            compiler_hook_seed_map[d.contract_address] = d.contract_hook_seed;
        }
    }

    auto monad_vm = create_monad_vm(args, engine, compiler_hook_seed_map);

    auto initial_state_ = initial_state();

    auto evmone_state = State{initial_state_};
    auto monad_state = State{initial_state_};

    auto exit_code_stats = std::unordered_map<evmc_status_code, std::size_t>{};
    auto total_messages = std::size_t{0};

    auto start_time = std::chrono::high_resolution_clock::now();

    iteration_index = 0;
    for (auto const &iteration : run) {
        std::visit(
            monad::vm::Cases{
                [&](DeployContract const &d) {
                    deploy_contracts(
                        evmone_state,
                        monad_state,
                        d.contract_address,
                        compile_program(d.contract));
                },
                [&](DeployPrecompile const &d) {
                    deploy_delegated_contracts(
                        evmone_state,
                        monad_state,
                        d.contract_address,
                        d.precompile_address);
                },
                [&](DeployDelegatedContract const &d) {
                    deploy_delegated_contracts(
                        evmone_state,
                        monad_state,
                        d.contract_address,
                        d.delegatee_address);
                },
                [&](SendMessage const &send) {
                    ++total_messages;

                    auto const ec = fuzz_iteration(
                        send.message,
                        rev,
                        evmone_state,
                        evmone_vm,
                        monad_state,
                        monad_vm,
                        args.implementation);
                    ++exit_code_stats[ec];
                }},
            iteration);

        iteration_index++;
    }

    if (verbose) {
        log_run(
            start_time,
            args,
            exit_code_stats,
            run_index,
            iteration_index,
            total_messages);
    }
}

static std::optional<FuzzerAssertFailure>
try_run(arguments const &args, Run const &run)
{
    try {
        size_t iteration_index = 0;
        do_run(0, args, false, run, iteration_index);
        return std::nullopt;
    }
    catch (FuzzerAssertFailure const &ex) {
        return ex;
    }
}

static void print_run_summary(Run const &run)
{
    size_t deploy_count = 0;
    size_t message_count = 0;
    size_t basic_block_count = 0;
    size_t instruction_count = 0;
    for (auto const &step : run) {
        std::visit(
            monad::vm::Cases{
                [&](DeployContract const &d) {
                    deploy_count++;
                    basic_block_count += d.contract.size();
                    for (BasicBlock const &bb : d.contract) {
                        instruction_count += bb.instructions.size();
                    }
                },
                [&](SendMessage const &) { message_count++; },
                [&](auto const &) {},
            },
            step);
    }
    std::cerr << "===== Run summary =====\n";
    std::cerr << "Contracts: " << deploy_count << "\n";
    std::cerr << "Messages: " << message_count << "\n";
    std::cerr << "Total basic blocks: " << basic_block_count << "\n";
    std::cerr << "Total instructions: " << instruction_count << "\n";
}

void print_message(evmc_message const &msg)
{
    static auto kind_map = std::map<evmc_call_kind, std::string>{
        {EVMC_CALL, "CALL"},
        {EVMC_CALLCODE, "CALLCODE"},
        {EVMC_DELEGATECALL, "DELEGATECALL"},
        {EVMC_CREATE, "CREATE"},
        {EVMC_CREATE2, "CREATE2"},
        {EVMC_EOFCREATE, "EVMC_EOFCREATE"},
    };

    std::cerr << fmt::format(
        "  kind {}, gas {}, value {}\n",
        kind_map[msg.kind],
        msg.gas,
        intx::hex(intx::be::load<intx::uint256>(msg.value)));

    std::cerr << fmt::format(
        "  code_address {}, sender {}, recipient {}\n",
        address(msg.code_address),
        address(msg.sender),
        address(msg.recipient));

    std::cerr << "  input_data [" << msg.input_size << " bytes]: ";
    for (size_t i = 0; i < msg.input_size; ++i) {
        std::cerr << fmt::format("{:02x}", msg.input_data[i]);
    }
    std::cerr << "\n";
}

void print_run(Run const &run)
{
    std::cerr << "Run with " << run.size() << " steps\n";
    for (size_t i = 0; i < run.size(); ++i) {

        std::visit(
            monad::vm::Cases{
                [&](DeployContract const &d) {
                    auto const program = compile_program(d.contract);
                    auto const code_hash =
                        evmone::keccak256(to_byte_string_view(program));
                    auto const code_hash_str = intx::hex(
                        intx::be::load<intx::uint256>(code_hash.bytes));
                    std::cerr << fmt::format(
                        "Iteration {}: Deploy contract (hash {}) at address {} "
                        "(size: {} bytes)\n",
                        i,
                        code_hash_str,
                        d.contract_address,
                        program.size());

                    // FIXME: Use revision from args
                    auto const &ir =
                        monad::vm::compiler::basic_blocks::unsafe_make_ir<
                            EvmTraits<EVMC_LATEST_STABLE_REVISION>>(program);
                    for (auto const &block : ir.blocks()) {
                        std::cerr << std::format("{}", block) << "\n";
                    }
                },
                [&](DeployPrecompile const &d) {
                    std::cerr << fmt::format(
                        "Iteration {}: Deploy precompile contract at address "
                        "{} delegating to precompile at address {}\n",
                        i,
                        d.contract_address,
                        d.precompile_address);
                },
                [&](DeployDelegatedContract const &d) {
                    std::cerr << fmt::format(
                        "Iteration {}: Deploy delegated contract at address {} "
                        "delegating to contract at address {}\n",
                        i,
                        d.contract_address,
                        d.delegatee_address);
                },
                [&](SendMessage const &send) {
                    std::cerr
                        << fmt::format("Iteration {}: Send message:\n", i);
                    print_message(send.message);
                }},
            run[i]);
    }
}

static std::optional<FuzzerAssertFailure> try_run_with_subcontract(
    arguments const &args, Run run, std::vector<BasicBlock> subcontract,
    std::size_t subcontract_iteration_index)
{
    FUZZER_ASSERT(std::holds_alternative<DeployContract>(
        run[subcontract_iteration_index]));
    DeployContract const &d =
        std::get<DeployContract>(run[subcontract_iteration_index]);
    run[subcontract_iteration_index] =
        DeployContract{d.contract_hook_seed, d.contract_address, subcontract};
    return try_run(args, run);
}

// A singleton run is one with a single contract and a single message.
template <typename Engine>
static std::optional<std::vector<BasicBlock>> shrink_run_contract(
    arguments const &args, Engine &engine, Run &run,
    std::size_t contract_iteration_index)
{
    FUZZER_ASSERT(
        std::holds_alternative<DeployContract>(run[contract_iteration_index]));
    auto contract =
        std::get<DeployContract>(run[contract_iteration_index]).contract;

    if (contract.size() == 0) {
        return std::nullopt;
    }

    auto [new_contract, removed_block_ix] = shrink_contract(engine, contract);
    if (try_run_with_subcontract(
            args, run, new_contract, contract_iteration_index)) {
        // Block was not needed
        return std::move(new_contract);
    }
    else if (contract[removed_block_ix].instructions.size() > 0) {
        // Try to remove instructions from the block instead
        // First try with ranges of instructions
        // Idea if that fails: Substitute instructions with simpler ones?
        auto new_contract2 = shrink_block(engine, contract, removed_block_ix);
        if (try_run_with_subcontract(
                args, run, new_contract2, contract_iteration_index)) {
            return std::move(new_contract2);
        }
    }
    else {
        // Block is empty but cannot be removed. This can only happen if
        // the block is a JUMPDEST and the next block is not a JUMPDEST
        // and depends on the fallthrough from the JUMPDEST block.
        auto [new_contract, shrunk_contract] =
            propagate_jumpdest(contract, removed_block_ix);
        if (shrunk_contract &&
            try_run_with_subcontract(
                args, run, new_contract, contract_iteration_index)) {
            return std::move(new_contract);
        }
    }

    return std::nullopt;
}

static Run make_singleton_run(
    seed_t contract_hook_seed, std::vector<BasicBlock> contract,
    evmc::address contract_address, evmc_message failed_message)
{
    return {
        DeployContract{contract_hook_seed, contract_address, contract},
        SendMessage{failed_message}};
}

static std::optional<FuzzerAssertFailure> try_singleton_run(
    arguments const &args, seed_t contract_hook_seed,
    std::vector<BasicBlock> contract, evmc::address contract_address,
    evmc_message failed_message)
{
    auto run = make_singleton_run(
        contract_hook_seed, contract, contract_address, failed_message);
    return try_run(args, run);
}

// A singleton run is one with a single contract and a single message.
static Run shrink_singleton_run(
    arguments const &args, seed_t contract_hook_seed,
    std::vector<BasicBlock> original_contract, evmc::address contract_address,
    evmc_message failed_message)
{
    auto engine = random_engine_t(args.seed);
    auto iteration_count = 0u;
    auto run = make_singleton_run(
        contract_hook_seed,
        original_contract,
        contract_address,
        failed_message);

    while (++iteration_count < args.contract_shrinking_attempts) {
        if (auto new_contract = shrink_run_contract(args, engine, run, 0)) {
            run[0] = DeployContract{
                contract_hook_seed, contract_address, new_contract.value()};
            iteration_count = 0;
            if (args.print_shrinker_state) {
                print_run_summary(run);
            }
        }
    }

    // Make sure the final shrunken contract still fails
    FUZZER_ASSERT(try_run(args, run));

    return run;
}

template <typename Engine>
static Run
shrink_remove_steps(arguments const &args, Engine &engine, Run const &run)
{
    auto current_run = run;

    auto iteration_count = 0u;
    while (++iteration_count < args.run_shrinking_attempts) {
        if (current_run.size() <= 2) { // Cannot shrink further than 2 steps
            break;
        }

        // Try to remove 10% of the steps
        auto const new_run = erase_range(engine, current_run, 0.1);

        if (try_run(args, new_run)) {
            current_run = std::move(new_run);
            iteration_count = 0;
            if (args.print_shrinker_state) {
                print_run_summary(current_run);
            }
        }
    }

    return current_run;
}

template <typename Engine>
static Run shrink_steps(arguments const &args, Engine &engine, Run const &run)
{
    auto current_run = run;

    auto iteration_count = 0u;
    while (++iteration_count < args.contract_shrinking_attempts) {

        // Pick any of the step and try to reduce it
        auto const element_to_shrink = std::uniform_int_distribution<size_t>(
            0, static_cast<size_t>(current_run.size()) - 1)(engine);

        std::visit(
            monad::vm::Cases{
                [&](DeployContract const &d) {
                    if (auto new_contract = shrink_run_contract(
                            args, engine, current_run, element_to_shrink)) {
                        // As instructions are removed from the contract, the
                        // state of the compiler hook RNG shifts, potentially
                        // changing its effects on instructions following the
                        // remove instructions. This can lead to false negatives
                        // when shrinking, where the shrinker thinks the smaller
                        // contract does not reproduce the failure, when in fact
                        // it would if the hook RNG state was the same.
                        //
                        // As a example, consider the following pseudo code:
                        //
                        // /--------------
                        // | Block:      |
                        // |   push N    |
                        // |   push M    |
                        // |   instr_A   |
                        // |   instr_B   |
                        // ---------------/
                        //
                        // Where instr_A is not relevant to the counter-example,
                        // but instr_B is and depends on the compiler hook
                        // state. instr_A cannot be removed without changing the
                        // hook state for instr_B, and so will never be removed.
                        //
                        // To mitigate this, we randomly try different seeds
                        // when shrinking the contract with a 5% change. Most
                        // counter-examples can be shrunk without this, so this
                        // feature is off by default.
                        //
                        // Idea: Try to shrink without this first, and have a
                        //       second shrinking pass with this enabled?
                        auto const new_seed =
                            toss(engine, args.shrink_contract_seed ? 0.05 : 0)
                                ? engine()
                                : d.contract_hook_seed;

                        current_run[element_to_shrink] = DeployContract{
                            new_seed, d.contract_address, new_contract.value()};
                        iteration_count = 0;
                        if (args.print_shrinker_state) {
                            print_run_summary(current_run);
                        }
                    }
                },
                [&](auto const &) {
                    // Cannot shrink other steps
                }},
            current_run[element_to_shrink]);
    }

    return current_run;
}

static Run shrink_complete_run(
    arguments const &args, Run const &run, size_t failed_iteration_index)
{
    auto engine = random_engine_t(args.seed);
    auto current_run = run;

    (void)failed_iteration_index;

    // First trim the steps after failed_iteration_index
    current_run.erase(
        current_run.begin() + static_cast<ptrdiff_t>(failed_iteration_index) +
            1,
        current_run.end());

    // Make sure the final shrunken run still fails
    FUZZER_ASSERT(try_run(args, current_run));

    print_run_summary(current_run);
    current_run = shrink_remove_steps(args, engine, current_run);
    current_run = shrink_steps(args, engine, current_run);
    // For multi-contract runs, we try to shrink a bit more in case shrinking
    // the contracts enabled further step removals.
    if (current_run.size() > 2) {
        current_run = shrink_remove_steps(args, engine, current_run);
        current_run = shrink_steps(args, engine, current_run);
    }

    // Make sure the final shrunken run still fails
    FUZZER_ASSERT(try_run(args, current_run));

    return current_run;
}

static Run
shrink_run(arguments const &args, Run const &run, size_t failed_iteration_index)
{
    // Assume that the contract that failed didn't depend on any of the previous
    // contracts. This is not always true, but most counter-examples are of this
    // form.
    // Prepare a run with only the msg.recipient contract and the message that
    // caused the failure.
    auto contract_map = std::unordered_map<
        evmc::address,
        std::pair<std::vector<BasicBlock>, seed_t>>{};
    for (auto const &step : run) {
        if (std::holds_alternative<DeployContract>(step)) {
            auto const &d = std::get<DeployContract>(step);
            contract_map.insert(
                {d.contract_address, {d.contract, d.contract_hook_seed}});
        }
    }

    auto const &failed_iteration = run[failed_iteration_index];
    if (!std::holds_alternative<SendMessage>(failed_iteration)) {
        std::cerr << "Failed iteration is not a message send\n";
        return run;
    }
    auto const &failed_message =
        std::get<SendMessage>(failed_iteration).message;
    auto const &failed_contract_it =
        contract_map.find(failed_message.code_address);
    if (failed_contract_it == contract_map.end()) {
        std::cerr << "Failed to find contract that caused the failure\n";
        return run;
    }
    auto const &failed_contract = failed_contract_it->second;

    if (!try_singleton_run(
            args,
            failed_contract.second,
            failed_contract.first,
            failed_message.code_address,
            failed_message)) {
        std::cerr << "Shrinker: Contract depends on other contracts or state\n";
        return shrink_complete_run(args, run, failed_iteration_index);
    }
    else {
        return shrink_singleton_run(
            args,
            failed_contract.second,
            failed_contract.first,
            failed_message.code_address,
            failed_message);
    }
}

static void run_loop(int argc, char **argv)
{
    auto args = parse_args(argc, argv);
    if (args.focus_path) {
        args.focus = parse_generator_focus(*args.focus_path);
    }
    auto const *msg_rev = evmc_revision_to_string(args.revision);
    for (auto i = 0u; i < args.runs; ++i) {
        std::cerr << std::format(
            "Fuzzing with seed @ {}: {}\n", msg_rev, args.seed);

        auto const start_time = std::chrono::high_resolution_clock::now();
        auto const &run = prepare_run(args);
        log_prepare(start_time, i, run.size());
        size_t iteration_index = 0;
        try {
            do_run(i, args, true, run, iteration_index);
        }
        catch (FuzzerAssertFailure const &ex) {
            // Disable stats printing while shrinking to reduce noise.
            args.print_stats = false;
            // Test whether the counter-example depends on the stack shuffling
            // introduced by the compiler hook. If so, we increase the number of
            // shrinking attempts by 10x to account for the non-determinism
            // and potential false negatives when shrinking.
            auto const deterministic_compilation_enabled =
                args.deterministic_compilation;
            args.deterministic_compilation = true;
            if (!deterministic_compilation_enabled && !try_run(args, run)) {
                args.contract_shrinking_attempts *= 10;
            }
            args.deterministic_compilation = deterministic_compilation_enabled;

            auto const &shrunk_run = shrink_run(args, run, iteration_index);
            std::cerr << "Counter-example found by fuzzer:\n";
            print_run(shrunk_run);

            auto const reason = try_run(args, shrunk_run);
            if (reason) {
                std::cerr << "Final failure reason:\n";
                std::cerr << std::format(
                    "  Assertion failed: {}\n", reason->what());
            }
            else {
                std::cerr << "ERROR: Final run succeeded unexpectedly\n";
            }

            std::exit(1);
        }
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
