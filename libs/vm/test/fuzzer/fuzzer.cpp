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

#include <monad/vm/compiler/ir/x86/types.hpp>
#include <monad/vm/core/assert.h>
#include <monad/vm/evm/opcodes.hpp>
#include <monad/vm/fuzzing/generator/choice.hpp>
#include <monad/vm/fuzzing/generator/generator.hpp>
#include <monad/vm/utils/debug.hpp>

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

static evmc::address deploy_contract(
    State &state, evmc::address const &from,
    std::span<std::uint8_t const> const code_)
{
    auto code = bytes{code_.data(), code_.size()};

    auto const create_address =
        compute_create_address(from, state.get_or_insert(from).nonce++);
    MONAD_VM_DEBUG_ASSERT(state.find(create_address) == nullptr);

    state.insert(
        create_address,
        Account{
            .nonce = 0,
            .balance = 0,
            .code_hash = evmone::keccak256(code),
            .storage = {},
            .transient_storage = {},
            .code = code});

    MONAD_VM_ASSERT(state.find(create_address) != nullptr);

    return create_address;
}

static evmc::address deploy_delegated_contract(
    State &state, evmc::address const &from, evmc::address const &delegatee)
{
    std::vector<uint8_t> code = {0xef, 0x01, 0x00};
    code.append_range(delegatee.bytes);
    MONAD_VM_ASSERT(code.size() == 23);
    return deploy_contract(state, from, code);
}

static evmc::address deploy_delegated_contracts(
    State &evmone_state, State &monad_state, evmc::address const &from,
    evmc::address delegatee)
{
    auto const a = deploy_delegated_contract(evmone_state, from, delegatee);
    auto const a1 = deploy_delegated_contract(monad_state, from, delegatee);
    MONAD_VM_ASSERT(a == a1);
    assert_equal(evmone_state, monad_state);
    return a;
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
        "-n,--messages",
        args.messages,
        "Number of messages to send per iteration (default 4)");

    app.add_option(
        "--seed",
        args.seed,
        "Seed to use for reproducible fuzzing (random by default)");

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
    std::bernoulli_distribution dist(p);
    return dist(engine);
}

static void do_run(std::size_t const run_index, arguments const &args)
{
    auto const rev = args.revision;

    std::cerr << std::format(
        "Fuzzing with seed @ {}: {}\n",
        evmc_revision_to_string(rev),
        args.seed);

    auto engine = random_engine_t(args.seed);

    auto evmone_vm = evmc::VM(evmc_create_evmone());
    auto monad_vm = create_monad_vm(args, engine);

    auto initial_state_ = initial_state();

    auto evmone_state = State{initial_state_};
    auto monad_state = State{initial_state_};

    auto contract_addresses = std::vector<evmc::address>{};

    auto exit_code_stats = std::unordered_map<evmc_status_code, std::size_t>{};
    auto total_messages = std::size_t{0};

    auto start_time = std::chrono::high_resolution_clock::now();

    for (auto i = 0; i < args.iterations_per_run; ++i) {
        using monad::vm::fuzzing::GeneratorFocus;
        auto focus = discrete_choice<GeneratorFocus>(
            engine,
            [](auto &) { return GeneratorFocus::Generic; },
            Choice(0.60, [](auto &) { return GeneratorFocus::Pow2; }),
            Choice(0.05, [](auto &) { return GeneratorFocus::DynJump; }));

        if (toss(engine, 0.001)) {
            auto pre_compile =
                monad::vm::fuzzing::generate_pre_compile_address(engine, rev);
            contract_addresses.push_back(pre_compile);

            if (rev >= EVMC_PRAGUE) {
                auto const a = deploy_delegated_contracts(
                    evmone_state, monad_state, genesis_address, pre_compile);
                contract_addresses.push_back(a);
            }
            continue;
        }

        for (;;) {
            auto const contract = monad::vm::fuzzing::generate_program(
                focus, engine, contract_addresses);
            if (contract.size() > evmone::MAX_CODE_SIZE) {
                // The evmone host will fail when we attempt to deploy
                // contracts of this size. It rarely happens that we
                // generate contract this large.
                std::cerr << "Skipping contract of size: " << contract.size()
                          << " bytes" << std::endl;
                continue;
            }

            auto const a =
                deploy_contract(evmone_state, genesis_address, contract);
            auto const a1 =
                deploy_contract(monad_state, genesis_address, contract);
            MONAD_VM_ASSERT(a == a1);

            assert_equal(evmone_state, monad_state);

            contract_addresses.push_back(a);

            if (args.revision >= EVMC_PRAGUE && toss(engine, 0.1)) {
                auto const b = deploy_delegated_contracts(
                    evmone_state, monad_state, genesis_address, a);
                contract_addresses.push_back(b);
            }
            break;
        }

        for (auto j = 0u; j < args.messages; ++j) {
            auto const target =
                monad::vm::fuzzing::uniform_sample(engine, contract_addresses);
            auto msg = monad::vm::fuzzing::generate_message(
                focus,
                engine,
                target,
                contract_addresses,
                {genesis_address},
                [&](auto const &address) {
                    if (auto *found = evmone_state.find(address);
                        found != nullptr) {
                        return found->code;
                    }

                    return evmc::bytes{};
                });
            ++total_messages;

            auto const ec = fuzz_iteration(
                *msg,
                rev,
                evmone_state,
                evmone_vm,
                monad_state,
                monad_vm,
                args.implementation);
            ++exit_code_stats[ec];
        }
    }

    log(start_time, args, exit_code_stats, run_index, total_messages);
}

static void run_loop(int argc, char **argv)
{
    auto args = parse_args(argc, argv);
    for (auto i = 0u; i < args.runs; ++i) {
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
