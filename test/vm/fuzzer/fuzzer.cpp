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

#include <test/utils/test_state.hpp>
#include <test/vm/utils/test_block_hash_buffer.hpp>
#include <test/vm/utils/test_host.hpp>

#include <category/core/address.hpp>
#include <category/core/assert.h>
#include <category/core/bytes.hpp>
#include <category/execution/ethereum/chain/ethereum_mainnet.hpp>
#include <category/execution/ethereum/core/transaction.hpp>
#include <category/execution/ethereum/create_contract_address.hpp>
#include <category/execution/ethereum/db/test/commit_simple.hpp>
#include <category/execution/ethereum/state2/block_state.hpp>
#include <category/execution/ethereum/state3/state.hpp>
#include <category/vm/compiler/ir/x86/types.hpp>
#include <category/vm/evm/opcodes.hpp>
#include <category/vm/fuzzing/generator/choice.hpp>
#include <category/vm/fuzzing/generator/generator.hpp>
#include <category/vm/memory_pool.hpp>
#include <category/vm/utils/debug.hpp>

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

using namespace monad;
using namespace monad::literals;
using namespace monad::vm::fuzzing;
using namespace std::chrono_literals;

using monad::test::TestBlockHashBuffer;
using monad::test::TestStateRef;
using enum monad::vm::compiler::EvmOpCode;
using monad::vm::compiler::native::CompilerConfig;

struct InterpreterFuzzerVmVariant
{
};

enum class FuzzerVmTag
{
    Compiler,
    Interpreter
};

class BlockNumberState
{
    uint64_t prev_block_number{};

public:
    uint64_t next()
    {
        return ++prev_block_number;
    }
};

using FuzzerVm =
    std::variant<evmc::VM, CompilerConfig, InterpreterFuzzerVmVariant>;

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

static constexpr Address genesis_address =
    monad::address_from_hex("0xBEEFCAFE000000000000000000000000BA5EBA11");

struct TransitionState
{
    TestStateRef test_state;
    vm::VM vm;
    BlockState block_state;
    State state;

    static constexpr vm::VM::Mode vm_mode(FuzzerVm const &execution_vm)
    {
        return std::holds_alternative<CompilerConfig>(execution_vm)
                   ? vm::VM::CompilerOnly
                   : vm::VM::InterpreterOnly;
    }

    TransitionState(TestStateRef ts, FuzzerVm &execution_vm)
        : test_state{ts}
        , vm{vm_mode(execution_vm)}
        , block_state{ts->trie_db, vm}
        , state{block_state, Incarnation{0, 0}}
    {
        if (std::holds_alternative<evmc::VM>(execution_vm)) {
            auto &e = std::get<evmc::VM>(execution_vm);
            vm.set_execute_override(
                [&e](
                    auto const *const host,
                    auto *const context,
                    auto const rev,
                    auto const *const msg,
                    auto const *const code,
                    auto const code_size) -> evmc::Result {
                    return e.execute(
                        *host, context, rev, *msg, code, code_size);
                });
        }
        else if (std::holds_alternative<CompilerConfig>(execution_vm)) {
            auto const &config = std::get<CompilerConfig>(execution_vm);
            vm.set_compiler_config(config);
        }
        state.push();
    }

    void accept(uint64_t block_number)
    {
        state.pop_accept();
        commit(block_number);
    }

    void reject()
    {
        state.pop_reject();
    }

private:
    void commit(uint64_t block_number)
    {
        block_state.merge(state);
        auto [released_state, released_code] = std::move(block_state).release();
        test::commit_simple(
            test_state->trie_db,
            *released_state,
            released_code,
            NULL_HASH_BLAKE3,
            BlockHeader{.number = block_number});
    }
};

static constexpr auto block_gas_limit = 300'000'000;

static Transaction
tx_from(TransitionState &tstate, evmc_message const &msg) noexcept
{
    auto tx = Transaction{};
    tx.to = msg.recipient;
    tx.gas_limit = block_gas_limit;
    tx.nonce = tstate.state.get_nonce(msg.sender);
    return tx;
}

template <Traits traits>
static evmc::Result message_call(
    TransitionState &tstate, BlockHashBuffer const &block_hash_buffer,
    Transaction const &tx, evmc_message const &msg,
    BlockHeader const &block_header)
{
    std::optional<uint256_t> base_fee_per_gas{};
    std::vector<std::optional<Address>> authorities{};
    EthereumMainnet const chain{};

    auto test_host = test::TestHost<traits>{
        block_hash_buffer,
        tstate.state,
        tx,
        msg.sender,
        base_fee_per_gas,
        authorities,
        block_header,
        chain};
    auto &host = test_host.get_evmc_host();
    return host.call(msg);
}

static evmc::Result transition(
    TransitionState &tstate, evmc_message const &msg, evmc_revision const rev,
    BlockHashBuffer const &block_hash_buffer, BlockHeader const &block_header)
{
    tstate.state.access_account(msg.sender); // tx sender is always warm

    auto tx = tx_from(tstate, msg);

    MONAD_ASSERT(tx.to.has_value());
    tstate.state.access_account(*tx.to);
    tstate.state.add_to_balance(*tx.to, intx::be::load<uint256_t>(msg.value));

    tstate.state.set_nonce(msg.sender, tstate.state.get_nonce(msg.sender) + 1);

    MONAD_ASSERT(rev == EVMC_OSAKA); // TODO switch to monad revisions
    using traits = EvmTraits<EVMC_OSAKA>;
    return message_call<traits>(
        tstate, block_hash_buffer, tx, msg, block_header);
}

static Address deploy_contract(
    TransitionState &tstate, std::span<std::uint8_t const> const code)
{
    auto const nonce = tstate.state.get_nonce(genesis_address);
    tstate.state.set_nonce(genesis_address, nonce + 1);

    auto const create_address = create_contract_address(genesis_address, nonce);
    MONAD_ASSERT(!tstate.state.account_exists(create_address));

    tstate.state.create_account_no_rollback(create_address);
    tstate.state.set_code(create_address, {code.data(), code.size()});

    MONAD_ASSERT(tstate.state.account_exists(create_address));
    auto const vcode = tstate.state.get_code(create_address);
    auto const &icode = vcode->intercode();
    MONAD_ASSERT(
        byte_string_view(code.data(), code.size()) ==
        byte_string_view(icode->code(), icode->size()));

    return create_address;
}

static Address deploy_contracts(
    TestStateRef evmone_state, FuzzerVm &evmone_vm, TestStateRef monad_state,
    FuzzerVm &monad_vm, std::span<std::uint8_t const> const code,
    uint64_t block_number)
{
    TransitionState evmone_tstate{evmone_state, evmone_vm};
    TransitionState monad_tstate{monad_state, monad_vm};
    auto const a = deploy_contract(evmone_tstate, code);
    auto const a1 = deploy_contract(monad_tstate, code);
    MONAD_ASSERT(a == a1);
    assert_equal(evmone_tstate.state, monad_tstate.state);
    evmone_tstate.accept(block_number);
    monad_tstate.accept(block_number);
    return a;
}

static Address
deploy_delegated_contract(TransitionState &tstate, Address const &delegatee)
{
    std::vector<uint8_t> code = {0xef, 0x01, 0x00};
    code.append_range(delegatee.bytes);
    MONAD_ASSERT(code.size() == 23);
    return deploy_contract(tstate, code);
}

static Address deploy_delegated_contracts(
    TestStateRef evmone_state, FuzzerVm &evmone_vm, TestStateRef monad_state,
    FuzzerVm &monad_vm, Address delegatee, uint64_t block_number)
{
    TransitionState evmone_tstate{evmone_state, evmone_vm};
    TransitionState monad_tstate{monad_state, monad_vm};
    auto const a = deploy_delegated_contract(evmone_tstate, delegatee);
    auto const a1 = deploy_delegated_contract(monad_tstate, delegatee);
    MONAD_ASSERT(a == a1);
    assert_equal(evmone_tstate.state, monad_tstate.state);
    evmone_tstate.accept(block_number);
    monad_tstate.accept(block_number);
    return a;
}

static void
set_genesis_balance(TestStateRef state, FuzzerVm &vm, uint64_t block_number)
{
    // Set genesis account balance to some large balance, sufficiently small
    // so that token supply will not overflow uint256.
    constexpr auto balance = std::numeric_limits<uint256_t>::max() / 2;
    TransitionState tstate{state, vm};
    tstate.state.add_to_balance(genesis_address, balance);
    MONAD_ASSERT(tstate.state.get_balance(genesis_address) == balance);
    tstate.accept(block_number);
}

static void set_genesis_balances(
    TestStateRef evmone_state, FuzzerVm &evmone_vm, TestStateRef monad_state,
    FuzzerVm &monad_vm, uint64_t block_number)
{
    set_genesis_balance(evmone_state, evmone_vm, block_number);
    set_genesis_balance(monad_state, monad_vm, block_number);
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
        FuzzerVmTag implementation = FuzzerVmTag::Compiler;
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

    auto const impl_map = std::map<std::string, FuzzerVmTag>{
        {"interpreter", FuzzerVmTag::Interpreter},
        {"compiler", FuzzerVmTag::Compiler},
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
    evmc_message const &msg, evmc_revision const rev,
    BlockHashBuffer const &block_hash_buffer, TestStateRef evmone_state,
    FuzzerVm &evmone_vm, TestStateRef monad_state, FuzzerVm &monad_vm,
    BlockHeader const &block_header)
{
    MONAD_ASSERT(
        evmone_state->trie_db.state_root() ==
        monad_state->trie_db.state_root());

    TransitionState evmone_tstate{evmone_state, evmone_vm};
    auto const evmone_result =
        transition(evmone_tstate, msg, rev, block_hash_buffer, block_header);

    TransitionState monad_tstate{monad_state, monad_vm};
    auto const monad_result =
        transition(monad_tstate, msg, rev, block_hash_buffer, block_header);

    assert_equal(
        evmone_result,
        monad_result,
        std::holds_alternative<InterpreterFuzzerVmVariant>(monad_vm));

    assert_equal(evmone_tstate.state, monad_tstate.state);

    if (monad_result.status_code == EVMC_SUCCESS) {
        evmone_tstate.accept(block_header.number);
        monad_tstate.accept(block_header.number);
    }
    else {
        evmone_tstate.reject();
        monad_tstate.reject();
    }

    MONAD_ASSERT(
        evmone_state->trie_db.state_root() ==
        monad_state->trie_db.state_root());

    return monad_result.status_code;
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
static CompilerConfig create_compiler_config(Engine &engine)
{
    return {
        .runtime_debug_trace =
            vm::utils::is_compiler_runtime_debug_trace_enabled,
        .max_code_size_offset = vm::interpreter::code_size_t::max(),
        .post_instruction_emit_hook = compiler_emit_hook(engine)};
}

template <typename Engine>
static FuzzerVm create_monad_vm(arguments const &args, Engine &engine)
{
    if (args.implementation == FuzzerVmTag::Compiler) {
        return create_compiler_config(engine);
    }
    return InterpreterFuzzerVmVariant{};
}

// Coin toss, biased whenever p != 0.5
template <typename Engine>
static bool toss(Engine &engine, double p)
{
    std::bernoulli_distribution dist(p);
    return dist(engine);
}

template <typename Engine>
static TestBlockHashBuffer generate_test_block_hash_buffer(Engine &engine)
{
    TestBlockHashBuffer b;
    for (size_t i = 0; i < BlockHashBuffer::N; ++i) {
        auto pre_hash = some_good_constant(engine).value;
        if (!pre_hash) {
            pre_hash = random_constant(engine).value;
        }
        b.set_blockhash(i, pre_hash.template store_be<bytes32_t>());
    }
    return b;
}

template <typename Engine>
static BlockHeader generate_block_header(Engine &engine, uint64_t block_number)
{
    auto pre_difficulty =
        some_good_constant(engine).value.template store_be<bytes32_t>();
    return BlockHeader{
        .parent_hash =
            some_good_constant(engine).value.template store_be<bytes32_t>(),
        .ommers_hash =
            some_good_constant(engine).value.template store_be<bytes32_t>(),
        .state_root =
            some_good_constant(engine).value.template store_be<bytes32_t>(),
        .transactions_root =
            some_good_constant(engine).value.template store_be<bytes32_t>(),
        .receipts_root =
            some_good_constant(engine).value.template store_be<bytes32_t>(),
        .prev_randao =
            some_good_constant(engine).value.template store_be<bytes32_t>(),
        .difficulty = intx::be::load<intx::uint256>(pre_difficulty),
        .number = block_number,
        .gas_limit = random_uint32(engine) % (block_gas_limit + 1),
        .gas_used = random_uint32(engine) % (block_gas_limit + 1),
        .timestamp = random_uint64(engine),
        .beneficiary = random_address(engine),
    };
}

static void do_run(
    monad::vm::MemoryPool &memory_pool, std::size_t const run_index,
    arguments const &args)
{
    auto const rev = args.revision;

    auto engine = random_engine_t(args.seed);

    auto evmone_vm = FuzzerVm(evmc::VM(evmc_create_evmone()));
    auto monad_vm = create_monad_vm(args, engine);

    auto evmone_state = std::make_shared<test::TestState>();
    auto monad_state = std::make_shared<test::TestState>();

    BlockNumberState block_counter;

    set_genesis_balances(
        evmone_state, evmone_vm, monad_state, monad_vm, block_counter.next());

    auto contract_addresses = std::vector<Address>{};
    auto known_addresses = std::vector<Address>{};

    auto exit_code_stats = std::unordered_map<evmc_status_code, std::size_t>{};
    auto total_messages = std::size_t{0};

    auto start_time = std::chrono::high_resolution_clock::now();

    auto block_hash_buffer = generate_test_block_hash_buffer(engine);

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
            auto precompile =
                monad::vm::fuzzing::generate_precompile_address(engine, rev);
            auto const a = deploy_delegated_contracts(
                evmone_state,
                evmone_vm,
                monad_state,
                monad_vm,
                precompile,
                block_counter.next());
            known_addresses.push_back(a);
        }

        for (;;) {
            auto const contract = monad::vm::fuzzing::generate_program(
                focus, engine, rev, known_addresses);

            if (contract.size() > evmone::MAX_CODE_SIZE) {
                // The evmone host will fail when we attempt to deploy
                // contracts of this size. It rarely happens that we
                // generate contract this large.
                std::cerr << "Skipping contract of size: " << contract.size()
                          << " bytes" << std::endl;
                continue;
            }

            auto const a = deploy_contracts(
                evmone_state,
                evmone_vm,
                monad_state,
                monad_vm,
                contract,
                block_counter.next());
            contract_addresses.push_back(a);
            known_addresses.push_back(a);

            if (args.revision >= EVMC_PRAGUE && toss(engine, 0.2)) {
                auto const b = deploy_delegated_contracts(
                    evmone_state,
                    evmone_vm,
                    monad_state,
                    monad_vm,
                    a,
                    block_counter.next());
                known_addresses.push_back(b);
            }
            break;
        }

        for (auto j = 0u; j < args.messages; ++j) {
            auto msg_memory = memory_pool.alloc_ref();
            auto msg = monad::vm::fuzzing::generate_message(
                focus,
                engine,
                contract_addresses,
                {genesis_address},
                [&](auto const &address) {
                    TransitionState tstate{monad_state, monad_vm};
                    return tstate.state.get_code(address);
                },
                msg_memory.get(),
                memory_pool.alloc_capacity());
            ++total_messages;

            auto const block_header =
                generate_block_header(engine, block_counter.next());
            block_hash_buffer.set_block_number(block_header.number);
            auto const ec = fuzz_iteration(
                *msg,
                rev,
                block_hash_buffer,
                evmone_state,
                evmone_vm,
                monad_state,
                monad_vm,
                block_header);
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
