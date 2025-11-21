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

#include <category/core/blake3.hpp>

#include <category/execution/ethereum/block_hash_buffer.hpp>
#include <category/execution/ethereum/chain/ethereum_mainnet.hpp>
#include <category/execution/ethereum/db/trie_db.hpp>
#include <category/execution/ethereum/execute_transaction.hpp>
#include <category/execution/ethereum/metrics/block_metrics.hpp>
#include <category/execution/ethereum/state2/block_state.hpp>
#include <category/execution/ethereum/state3/state.hpp>
#include <category/execution/ethereum/trace/call_tracer.hpp>
#include <category/execution/ethereum/trace/state_tracer.hpp>

#include <category/vm/compiler/ir/x86/types.hpp>
#include <category/vm/core/assert.h>
#include <category/vm/evm/opcodes.hpp>
#include <category/vm/fuzzing/generator/choice.hpp>
#include <category/vm/fuzzing/generator/generator.hpp>
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
#include <variant>
#include <vector>

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

static constexpr auto beneficiary_address =
    0x5353535353535353535353535353535353535353_address;

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
    init[beneficiary_address] = {};
    return init;
}

static void initial_state(TrieDb &tdb)
{

    auto const eth_header = BlockHeader{};

    bytes32_t const block_id =
        eth_header.number ? bytes32_t{eth_header.number} : NULL_HASH_BLAKE3;
    tdb.commit(
        StateDeltas{
            {genesis_address,
             StateDelta{
                 .account =
                     {std::nullopt,
                      Account{
                          .balance =
                              std::numeric_limits<intx::uint256>::max() / 2}}}},
            {beneficiary_address,
             StateDelta{.account = {std::nullopt, Account{}}}}},
        Code{},
        block_id,
        eth_header);
    tdb.finalize(eth_header.number, block_id);
    tdb.set_block_and_prefix(eth_header.number);
}

static evmone::state::Transaction
tx_from(evmone::state::State &state, evmc::address const &addr) noexcept
{
    auto tx = evmone::state::Transaction{};
    tx.gas_limit = block_gas_limit;
    tx.sender = addr;
    tx.nonce = state.get_or_insert(addr).nonce;
    return tx;
}

// Derived from the evmone transition implementation; transaction-related
// book-keeping is elided here to keep the implementation simple and allow us to
// send arbitrary messages to update the state.
static evmc::Result transition(
    evmone::state::State &state, evmc_message const &msg,
    evmc_revision const rev, evmc::VM &vm, std::int64_t const block_gas_left)
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
    auto block = evmone::state::BlockInfo{};
    auto hashes = evmone::test::TestBlockHashes{};
    auto tx = tx_from(state, msg.sender);
    tx.to = msg.recipient;

    constexpr auto effective_gas_price = 10;

    auto *sender_ptr = state.find(msg.sender);
    auto &sender_acc =
        (sender_ptr != nullptr) ? *sender_ptr : state.insert(msg.sender);

    ++sender_acc.nonce;
    sender_acc.balance -= block_gas_left * effective_gas_price;

    evmone::state::Host host{rev, vm, state, block, hashes, tx};

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
        [](std::pair<evmc::address const, evmone::state::Account> const
               &p) noexcept { return p.second.destructed; });

    // Delete empty accounts after every transaction. This is strictly required
    // until Byzantium where intermediate state root hashes are part of the
    // transaction receipt.
    // TODO: Consider limiting this only to Spurious Dragon.
    if (rev >= EVMC_SPURIOUS_DRAGON) {
        std::erase_if(
            state.get_modified_accounts(),
            [](std::pair<evmc::address const, evmone::state::Account> const
                   &p) noexcept {
                auto const &acc = p.second;
                return acc.erase_if_empty && acc.is_empty();
            });
    }

    return result;
}

static evmc::address deploy_contract(
    evmone::test::TestState &state, evmc::address const &from,
    std::span<std::uint8_t const> const code_, intx::uint256 balance = 0)
{
    auto code = evmc::bytes{code_.data(), code_.size()};

    state.try_emplace(from);

    auto const nonce = state[from].nonce++;
    // std::cerr << "nonce evmone: " << hex(from) << " " << nonce << "\n";
    auto const create_address =
        evmone::state::compute_create_address(from, nonce);
    MONAD_VM_DEBUG_ASSERT(state.find(create_address) == state.end());

    state[create_address] = evmone::test::TestAccount{
        .nonce = 0, .balance = balance, .storage = {}, .code = code};

    MONAD_VM_ASSERT(state.find(create_address) != state.end());

    return create_address;
}

static evmc::address deploy_contract(
    monad::State &state, evmc::address const &from,
    std::span<std::uint8_t const> const code_, intx::uint256 balance = 0)
{
    auto code = evmc::bytes{code_.data(), code_.size()};

    auto const nonce = state.get_nonce(from);
    state.set_nonce(from, nonce + 1);

    // std::cerr << "nonce mnad: " << hex(from) << " " << nonce << "\n";
    auto const create_address =
        evmone::state::compute_create_address(from, nonce);
    MONAD_VM_DEBUG_ASSERT(!state.account_exists(create_address));

    state.create_contract(create_address);
    state.set_code(create_address, code);
    state.add_to_balance(create_address, balance);

    MONAD_VM_ASSERT(state.account_exists(create_address));

    return create_address;
}

static evmc::address deploy_delegated_contract(
    evmone::test::TestState &state, evmc::address const &from,
    evmc::address const &delegatee)
{
    std::vector<uint8_t> code = {0xef, 0x01, 0x00};
    code.append_range(delegatee.bytes);
    MONAD_VM_ASSERT(code.size() == 23);
    return deploy_contract(state, from, code);
}

static evmc::address deploy_delegated_contract(
    monad::State &state, evmc::address const &from,
    evmc::address const &delegatee)
{
    std::vector<uint8_t> code = {0xef, 0x01, 0x00};
    code.append_range(delegatee.bytes);
    MONAD_VM_ASSERT(code.size() == 23);
    return deploy_contract(state, from, code);
}

using random_engine_t = std::mt19937_64;

namespace
{
    struct arguments
    {
        using seed_t = random_engine_t::result_type;
        static constexpr seed_t default_seed =
            std::numeric_limits<seed_t>::max();

        std::uint64_t iterations_per_run = 100;
        std::size_t messages = 4;
        seed_t seed = default_seed;
        std::size_t runs = std::numeric_limits<std::size_t>::max();
        bool print_stats = false;
        BlockchainTestVM::Implementation implementation =
            BlockchainTestVM::Implementation::Compiler;
        evmc_revision revision = EVMC_PRAGUE;
        std::optional<std::string> focus_path = std::nullopt;
        std::optional<GeneratorFocus> focus = std::nullopt;
        bool tx = false;

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
    app.add_flag("--tx", args.tx, "fuzz transactions insted o messages");

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

static evmc_status_code execute_message(
    evmc_message const &msg, evmc_revision const rev,
    evmone::test::TestState &state, evmc::VM &evmone_vm, evmc::VM &monad_vm,
    BlockchainTestVM::Implementation const impl)
{
    auto evmone_state = evmone::state::State{state};
    auto monad_state = evmone::state::State{state};

    for (evmone::state::State &state :
         {std::ref(evmone_state), std::ref(monad_state)}) {
        state.get_or_insert(msg.sender);
        state.get_or_insert(msg.recipient);
    }

    auto const evmone_result =
        transition(evmone_state, msg, rev, evmone_vm, block_gas_limit);

    auto const monad_result =
        transition(monad_state, msg, rev, monad_vm, block_gas_limit);

    assert_equal(
        evmone_result,
        monad_result,
        impl == BlockchainTestVM::Implementation::Interpreter);

    auto evm_diff = evmone_state.build_diff(rev);

    auto monad_diff = monad_state.build_diff(rev);

    assert_equal(evm_diff, monad_diff, state);

    if (evmone_result.status_code == EVMC_SUCCESS) {
        state.apply(evmone_state.build_diff(rev));
    }
    return evmone_result.status_code;
}

static monad::TransactionType
to_monad_tx_type(evmone::state::Transaction::Type tx_type)
{
    switch (tx_type) {
    case evmone::state::Transaction::Type::legacy:
        return monad::TransactionType::legacy;
    case evmone::state::Transaction::Type::access_list:
        return monad::TransactionType::eip2930;
    case evmone::state::Transaction::Type::eip1559:
        return monad::TransactionType::eip1559;
    case evmone::state::Transaction::Type::blob:
        return monad::TransactionType::eip4844;
    case evmone::state::Transaction::Type::set_code:
        return monad::TransactionType::eip7702;
    }
}

static monad::AccessList
to_monad_access_list(evmone::state::AccessList const &al)
{
    monad::AccessList mal;
    mal.reserve(al.size());

    for (auto const &a : al) {
        mal.emplace_back(a.first, a.second);
    }

    return mal;
}

static monad::AuthorizationList
to_monad_authorization_list(evmone::state::AuthorizationList const &al)
{
    monad::AuthorizationList mal;
    mal.reserve(al.size());

    for (auto const &a : al) {
        monad::SignatureAndChain sc = {.r = a.r, .s = a.s};
        sc.from_v(a.v);
        mal.emplace_back(sc, a.addr, a.nonce);
    }

    return mal;
}

static monad::Transaction to_monad_tx(evmone::state::Transaction const &tx)
{

    monad::SignatureAndChain sc = {
        .r = tx.r, .s = tx.s, .chain_id = tx.chain_id, .y_parity = tx.v};

    return monad::Transaction{
        .sc = sc,
        .nonce = tx.nonce,
        .max_fee_per_gas = tx.max_gas_price,
        .gas_limit = static_cast<uint64_t>(tx.gas_limit),
        .value = tx.value,
        .to = tx.to,
        .type = to_monad_tx_type(tx.type),
        .data = tx.data,
        .access_list = to_monad_access_list(tx.access_list),
        .max_priority_fee_per_gas = tx.max_priority_gas_price,
        .max_fee_per_blob_gas = tx.max_blob_gas_price,
        .blob_versioned_hashes = tx.blob_hashes,
        .authorization_list =
            to_monad_authorization_list(tx.authorization_list)};
}

class MonadBlockHashes : public evmone::state::BlockHashes
{
    monad::BlockHashBufferFinalized &_block_hash_buffer;

public:
    MonadBlockHashes(monad::BlockHashBufferFinalized &block_hash_buffer)
        : _block_hash_buffer{block_hash_buffer}
    {
    }

    evmc::bytes32 get_block_hash(int64_t block_number) const noexcept override
    {
        return _block_hash_buffer.get(static_cast<uint64_t>(block_number));
    }
};

static evmc_status_code execute_transaction(
    uint64_t block_no, uint64_t tx_no, evmone::state::Transaction const &tx,
    evmc_revision const rev, evmone::test::TestState &evmone_state,
    monad::BlockState &bs, monad::BlockHashBufferFinalized &block_hash_buffer,
    evmc::VM &evmone_vm, evmc::VM &, BlockchainTestVM::Implementation const)
{
    constexpr auto MIN_BASE_FEE_PER_BLOB_GAS = 1;
    constexpr auto BASE_FEE_PER_GAS = 10;

    auto block = evmone::state::BlockInfo{
        .number = static_cast<int64_t>(block_no),
        .coinbase = beneficiary_address,
        .parent_ommers_hash = NULL_LIST_HASH,
        .prev_randao = {},
        .parent_beacon_block_root = NULL_HASH,
        .base_fee = BASE_FEE_PER_GAS,
        .blob_gas_used = std::nullopt,
        .excess_blob_gas = std::nullopt,
        .blob_base_fee = MIN_BASE_FEE_PER_BLOB_GAS,
        .ommers = {},
        .withdrawals = {}};
    auto block_hashes = MonadBlockHashes{block_hash_buffer};

    auto const tx_props_or_error = evmone::state::validate_transaction(
        evmone_state,
        block,
        tx,
        rev,
        block_gas_limit,
        static_cast<int64_t>(evmone::state::max_blob_gas_per_block(rev)));
    if (std::holds_alternative<std::error_code>(tx_props_or_error)) {
        auto const &ec = std::get<std::error_code>(tx_props_or_error);
        std::cerr << "Transaction validation failed: " << ec.message() << "\n";
        return EVMC_FAILURE;
    }
    auto const &tx_props =
        std::get<evmone::state::TransactionProperties>(tx_props_or_error);

    auto const evmone_result = evmone::state::transition(
        evmone_state, block, block_hashes, tx, rev, evmone_vm, tx_props);

    // auto const monad_result =
    //     evmone::state::transition(evmone_state, block, block_hashes, tx, rev,
    //     monad_vm, tx_props);

    monad::BlockMetrics metrics;
    monad::BlockHeader const header{
        .number = block_no,
        .beneficiary = beneficiary_address,
        .base_fee_per_gas = BASE_FEE_PER_GAS};

    boost::fibers::promise<void> prev{};
    prev.set_value();

    monad::NoopCallTracer noop_call_tracer;
    trace::StateTracer noop_state_tracer = std::monostate{};

    auto const monad_tx = to_monad_tx(tx);

    Result<monad::Receipt> const monad_result2 =
        monad::ExecuteTransaction<EvmTraits<EVMC_PRAGUE>>(
            EthereumMainnet{},
            tx_no,
            monad_tx,
            tx.sender,
            {},
            header,
            block_hash_buffer,
            bs,
            metrics,
            prev,
            noop_call_tracer,
            noop_state_tracer)();
    if (!monad_result2) {
        std::cerr << "Transaction validation failed: "
                  << monad_result2.assume_error().message().c_str() << "\n";
        MONAD_VM_ASSERT(false);
    }

    evmone_state.apply(evmone_result.state_diff);
    auto const diff = evmone::state::finalize(
        evmone_state, rev, beneficiary_address, 0, {}, {});
    evmone_state.apply(diff);

    assert_equal(evmone_state, bs);
    return evmone_result.status;
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
    auto const per_contract =
        diff / static_cast<int64_t>(args.iterations_per_run);

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

bytes32_t dummy_block_id(uint64_t const seed)
{
    return to_bytes(blake3(mpt::serialize_as_big_endian<sizeof(seed)>(seed)));
}

static void do_run(std::size_t const run_index, arguments const &args)
{
    auto const rev = args.revision;

    auto engine = random_engine_t(args.seed);

    auto evmone_vm = evmc::VM(evmc_create_evmone());
    auto monad_vm = create_monad_vm(args, engine);

    auto initial_state_ = initial_state();

    InMemoryMachine machine;
    mpt::Db db{machine};
    TrieDb tdb{db};
    initial_state(tdb);

    vm::VM vm;

    BlockState block_state{tdb, vm};

    BlockHashBufferFinalized buf;
    buf.set(0, bytes32_t{1}); // genesis

    BlockHashChain chain(buf);
    bytes32_t parent_id;
    auto block_id = dummy_block_id(0);

    auto contract_addresses = std::vector<evmc::address>{};
    auto sender_addresses = std::vector<evmc::address>{};
    auto known_addresses = std::vector<evmc::address>{};

    auto exit_code_stats = std::unordered_map<evmc_status_code, std::size_t>{};
    auto total_messages = std::size_t{0};

    auto start_time = std::chrono::high_resolution_clock::now();

    for (uint64_t i = 1; i <= args.iterations_per_run; ++i) {
        State monad_state_temp{block_state, Incarnation{2 * i - 1, 0}};

        parent_id = block_id;
        block_id = dummy_block_id(2 * i - 1);
        chain.propose(bytes32_t{2 * i - 1}, 2 * i - 1, block_id, parent_id);

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
            auto const a = deploy_delegated_contract(
                initial_state_, genesis_address, precompile);
            auto const a2 = deploy_delegated_contract(
                monad_state_temp, genesis_address, precompile);
            MONAD_VM_ASSERT(a == a2);
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

            auto a = deploy_contract(initial_state_, genesis_address, contract);
            auto const a2 =
                deploy_contract(monad_state_temp, genesis_address, contract);
            MONAD_VM_ASSERT(a == a2);

            contract_addresses.push_back(a);
            known_addresses.push_back(a);

            auto sender_addr = deploy_contract(
                initial_state_,
                genesis_address,
                {},
                std::numeric_limits<intx::uint256>::max() / 2);
            auto sender_addr2 = deploy_contract(
                monad_state_temp,
                genesis_address,
                {},
                std::numeric_limits<intx::uint256>::max() / 2);
            MONAD_VM_ASSERT(sender_addr == sender_addr2);
            sender_addresses.push_back(sender_addr);

            if (args.revision >= EVMC_PRAGUE && toss(engine, 0.2)) {
                auto const b = deploy_delegated_contract(
                    initial_state_, genesis_address, a);
                auto const b2 = deploy_delegated_contract(
                    monad_state_temp, genesis_address, a);
                MONAD_VM_ASSERT(b == b2);
                known_addresses.push_back(b);
            }
            break;
        }

        block_state.merge(monad_state_temp);
        assert_equal(initial_state_, block_state);

        chain.finalize(block_id);
        parent_id = block_id;
        block_id = dummy_block_id(2 * i);
        chain.propose(bytes32_t{2 * i}, 2 * i, block_id, parent_id);

        if (args.tx) {
            for (auto j = 1u; j <= args.messages; ++j) {
                auto tx = monad::vm::fuzzing::generate_transaction(
                    focus,
                    engine,
                    contract_addresses,
                    sender_addresses,
                    {genesis_address},
                    [&](auto const &address) {
                        return initial_state_.get_account_code(address);
                    },
                    [&](auto const &address) {
                        auto nonce = initial_state_[address].nonce;
                        return nonce;
                    });
                ++total_messages;

                auto const ec = execute_transaction(
                    2 * i,
                    j,
                    tx,
                    rev,
                    initial_state_,
                    block_state,
                    buf,
                    evmone_vm,
                    monad_vm,
                    args.implementation);
                ++exit_code_stats[ec];
            }
        }
        else {
            for (auto j = 0u; j < args.messages; ++j) {
                auto msg = monad::vm::fuzzing::generate_message(
                    focus,
                    engine,
                    contract_addresses,
                    {genesis_address},
                    [&](auto const &address) {
                        return initial_state_.get_account_code(address);
                    });
                ++total_messages;

                auto const ec = execute_message(
                    *msg,
                    rev,
                    initial_state_,
                    evmone_vm,
                    monad_vm,
                    args.implementation);
                ++exit_code_stats[ec];
            }
        }
        chain.finalize(block_id);
    }

    log(start_time, args, exit_code_stats, run_index, total_messages);
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
