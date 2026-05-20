// Copyright (C) 2026 Category Labs, Inc.
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

// Witness round-trip fuzzer.
//
// Mirrors what blockchain_test.cpp does for JSON fixtures but driven by a
// pseudo-random generator instead of a corpus: for every "block" we
//   (1) deploy a few random contracts directly via State::set_code,
//   (2) drive a sequence of evmc_messages through EvmcHost<traits> against a
//       live BlockState (TrieDb-backed),
//   (3) collect StateDeltas + the codes read during execution,
//   (4) generate an execution witness from the live state trie,
//   (5) rebuild a PartialTrieDb from the witness,
//   (6) replay the same deploy+message sequence against the partial DB,
//   (7) commit both DBs and ASSERT their state roots match.
//
// We bypass tx signing the same way test/vm/fuzzer does: dummy Transaction
// for EvmcHost's reference field; manual sender nonce/balance bookkeeping.

#include <category/core/address.hpp>
#include <category/core/assert.h>
#include <category/core/byte_string.hpp>
#include <category/core/bytes.hpp>
#include <category/core/config.hpp>
#include <category/core/hex.hpp>
#include <category/core/int.hpp>
#include <category/core/keccak.hpp>
#include <category/execution/ethereum/block_hash_buffer.hpp>
#include <category/execution/ethereum/chain/chain.hpp>
#include <category/execution/monad/chain/monad_chain.hpp>
#include <category/execution/ethereum/core/account.hpp>
#include <category/execution/ethereum/core/block.hpp>
#include <category/execution/ethereum/core/fmt/bytes_fmt.hpp>
#include <category/execution/ethereum/core/transaction.hpp>
#include <category/execution/ethereum/create_contract_address.hpp>
#include <category/execution/ethereum/db/db.hpp>
#include <category/execution/ethereum/db/partial_trie_db.hpp>
#include <category/execution/ethereum/db/test/commit_simple.hpp>
#include <category/execution/ethereum/db/trie_db.hpp>
#include <category/execution/ethereum/db/util.hpp>
#include <category/execution/ethereum/db/witness_generator.hpp>
#include <category/execution/ethereum/evmc_host.hpp>
#include <category/execution/ethereum/rlp/execution_witness.hpp>
#include <category/execution/ethereum/state2/block_state.hpp>
#include <category/execution/ethereum/state2/state_deltas.hpp>
#include <category/execution/ethereum/state3/state.hpp>
#include <category/execution/ethereum/trace/call_tracer.hpp>
#include <category/execution/ethereum/trace/state_tracer.hpp>
#include <category/execution/ethereum/tx_context.hpp>
#include <category/execution/ethereum/types/incarnation.hpp>
#include <category/mpt/db.hpp>
#include <category/mpt/nibbles_view.hpp>
#include <category/vm/evm/monad/revision.h>
#include <category/vm/evm/switch_traits.hpp>
#include <category/vm/evm/traits.hpp>
#include <category/vm/fuzzing/generator/generator.hpp>
#include <category/vm/vm.hpp>

#include <evmc/evmc.h>
#include <evmc/evmc.hpp>

#include <CLI/CLI.hpp>

#include <chrono>
#include <cstdint>
#include <cstdlib>
#include <format>
#include <iostream>
#include <limits>
#include <map>
#include <memory>
#include <random>
#include <string>
#include <utility>
#include <variant>
#include <vector>

using namespace monad;
using namespace monad::literals;

namespace
{
    using random_engine_t = std::mt19937_64;
    using seed_t = random_engine_t::result_type;

    // A fixed funded sender baked into genesis. We never need this account's
    // private key because we bypass tx signing — only the address matters.
    constexpr Address SENDER =
        0xBEEFCAFE000000000000000000000000BA5EBA11_address;

    // Cap each call's gas to keep individual iterations cheap.
    constexpr int64_t MSG_GAS_LIMIT = 1'000'000;

    // Effective gas price used for manual sender bookkeeping. Matches
    // test/vm/fuzzer/fuzzer.cpp.
    constexpr uint64_t EFFECTIVE_GAS_PRICE = 10;

    // One iteration's worth of generated fuzz input. Re-used across the
    // live path and the witness-replay path so they execute identically.
    struct Iteration
    {
        // Contracts deployed by direct `state.set_code` at the start of the
        // iteration. Each Address is `create_contract_address(SENDER, nonce)`
        // with nonce taken from the sender at deploy time, so determinism
        // across live+witness paths just requires running deploys in the
        // same order against a sender with the same starting nonce.
        std::vector<byte_string> contract_codes;
        // Random calldata buffers. Stored as owning byte_strings so we can
        // build fresh evmc_message objects on each replay without worrying
        // about message-pool lifetime mismatches between paths.
        std::vector<byte_string> message_inputs;
        // Per-message (target_index, value). target_index indexes into the
        // contracts deployed in this iteration.
        struct Msg
        {
            evmc_call_kind kind;
            size_t target_idx;
            uint256_t value;
            uint8_t flags; // mostly 0; could be EVMC_STATIC.
        };
        std::vector<Msg> messages;
    };

    // Generate one iteration's worth of inputs from `engine`.
    template <typename Engine>
    Iteration generate_iteration(
        Engine &engine, evmc_revision const rev,
        vm::fuzzing::GeneratorFocus const &focus,
        size_t const num_contracts, size_t const num_messages)
    {
        Iteration iter;
        iter.contract_codes.reserve(num_contracts);
        iter.message_inputs.reserve(num_messages);
        iter.messages.reserve(num_messages);

        for (size_t i = 0; i < num_contracts; ++i) {
            auto prog =
                vm::fuzzing::generate_program(focus, engine, rev, {});
            // Cap to MAX_CODE_SIZE so deployment is always accepted.
            constexpr size_t cap = 24576;
            if (prog.size() > cap) {
                prog.resize(cap);
            }
            iter.contract_codes.emplace_back(prog.begin(), prog.end());
        }

        std::uniform_int_distribution<size_t> input_size_dist{0, 256};
        std::uniform_int_distribution<uint8_t> byte_dist{0, 255};
        std::uniform_int_distribution<size_t> tgt_dist{0, num_contracts - 1};
        std::array<evmc_call_kind, 3> const call_kinds{
            EVMC_CALL, EVMC_DELEGATECALL, EVMC_CALLCODE};
        std::uniform_int_distribution<size_t> kind_dist{
            0, call_kinds.size() - 1};

        for (size_t i = 0; i < num_messages; ++i) {
            byte_string input;
            size_t const sz = input_size_dist(engine);
            input.resize(sz);
            for (size_t k = 0; k < sz; ++k) {
                input[k] = byte_dist(engine);
            }
            iter.message_inputs.emplace_back(std::move(input));

            Iteration::Msg msg{};
            msg.kind = call_kinds[kind_dist(engine)];
            msg.target_idx = tgt_dist(engine);
            msg.value = 0; // keep value zero; non-zero requires more careful
                           // sender-balance bookkeeping under CALLCODE.
            msg.flags = 0;
            iter.messages.push_back(msg);
        }

        return iter;
    }

    // Materialize the EvmcHost<traits> + State, deploy the contracts, and
    // drive the messages. `deployed` is filled with addresses of the
    // newly-deployed contracts. Returns nothing — mutations are visible via
    // bs/state.
    template <Traits traits>
    void execute_iteration(
        Iteration const &iter, vm::VM &vm, BlockState & /*bs*/, State &state,
        trace::StateTracer &state_tracer, BlockHashBuffer const &hash_buffer,
        evmc_tx_context const &tx_context,
        ChainContext<traits> const &chain_ctx,
        std::vector<Address> &deployed)
    {
        deployed.clear();
        deployed.reserve(iter.contract_codes.size());

        NoopCallTracer call_tracer;
        Transaction const dummy_tx{}; // EvmcHost stores a reference but
                                      // never dereferences it for plain
                                      // host.call paths.
        std::optional<uint256_t> const base_fee{0};

        EvmcHost<traits> host{
            call_tracer,
            state_tracer,
            tx_context,
            hash_buffer,
            state,
            dummy_tx,
            base_fee,
            /*i=*/0,
            chain_ctx};

        // Sender must be access-warm so subsequent CALLs don't double-charge.
        state.access_account(SENDER);

        // Direct contract deploys: create_contract_address(SENDER, nonce),
        // bump nonce, write code, mark warm.
        for (auto const &code : iter.contract_codes) {
            uint64_t const sender_nonce = state.get_nonce(SENDER);
            Address const addr =
                create_contract_address(SENDER, sender_nonce);
            state.set_nonce(SENDER, sender_nonce + 1);

            state.create_contract(addr);
            state.set_code(addr, byte_string_view{code});
            state.access_account(addr);

            deployed.push_back(addr);
        }

        // Run messages. We mimic the bookkeeping in
        // test/vm/fuzzer/fuzzer.cpp:transition(): debit gas upfront,
        // call, refund leftover.
        for (size_t i = 0; i < iter.messages.size(); ++i) {
            auto const &m = iter.messages[i];

            uint64_t const sender_nonce = state.get_nonce(SENDER);
            uint256_t const charge =
                uint256_t{MSG_GAS_LIMIT} * EFFECTIVE_GAS_PRICE;
            if (state.get_balance(SENDER) < charge) {
                // Out of budget for the rest of the iteration.
                break;
            }
            state.subtract_from_balance(SENDER, charge);
            state.set_nonce(SENDER, sender_nonce + 1);

            Address const recipient = deployed[m.target_idx];

            auto msg_memory = vm.message_memory_ref();
            evmc_message msg{};
            msg.kind = m.kind;
            msg.flags = m.flags;
            msg.depth = 0;
            msg.gas = MSG_GAS_LIMIT;
            msg.recipient = recipient;
            msg.sender = SENDER;
            msg.input_data = iter.message_inputs[i].data();
            msg.input_size = iter.message_inputs[i].size();
            store_be(msg.value.bytes, m.value);
            msg.code_address = recipient;
            msg.memory_handle = msg_memory.get();
            msg.memory = msg_memory.get();
            msg.memory_capacity = vm.message_memory_capacity();

            auto const result = host.call(msg);

            int64_t const gas_used = MSG_GAS_LIMIT - result.gas_left;
            int64_t const gas_left_after_refund = MSG_GAS_LIMIT - gas_used;
            state.add_to_balance(
                SENDER,
                uint256_t{static_cast<uint64_t>(gas_left_after_refund)} *
                    EFFECTIVE_GAS_PRICE);
        }
    }

    template <Traits traits>
    bool run_block(
        random_engine_t &engine, mpt::Db &db, TrieDb &tdb, vm::VM &vm,
        uint64_t const block_number,
        vm::fuzzing::GeneratorFocus const &focus, size_t const contracts,
        size_t const messages_per_block)
    {
        // Pre-state-root snapshot — this is the anchor the witness
        // partial trie will be rebuilt against.
        bytes32_t const pre_state_root = tdb.state_root();

        // Generate iteration inputs once; replay against both DBs.
        Iteration const iter = generate_iteration(
            engine, traits::evm_rev(), focus, contracts, messages_per_block);

        // ===== Live path =====
        BlockHashBufferFinalized hash_buffer;
        // BLOCKHASH lookups should resolve against the just-finalized
        // genesis at block 0. The fuzzer only ever calls at block N>=1.
        evmc_tx_context const tx_ctx = EMPTY_TX_CONTEXT;
        auto const chain_ctx = ChainContext<traits>::debug_empty();

        BlockState bs_live{tdb, vm};
        State state_live{bs_live, Incarnation{block_number, 0}};
        trace::StateTracer state_tracer_live{trace::CodeTracer{}};

        std::vector<Address> deployed;
        execute_iteration<traits>(
            iter,
            vm,
            bs_live,
            state_live,
            state_tracer_live,
            hash_buffer,
            tx_ctx,
            chain_ctx,
            deployed);

        bs_live.merge(state_live);
        auto [deltas, code, sds_reads] = std::move(bs_live).release();

        // Collect read_codes from the live-path CodeTracer.
        Code read_codes;
        {
            auto *const ct =
                std::get_if<trace::CodeTracer>(&state_tracer_live);
            MONAD_ASSERT(ct != nullptr);
            for (auto const &kv : *ct->codes) {
                read_codes.emplace(kv.first, kv.second);
            }
        }

        // Walk the live state trie to assemble the witness nodes/codes.
        auto cursor_res = db.find(
            tdb.get_root(),
            mpt::concat(FINALIZED_NIBBLE, STATE_NIBBLE),
            block_number);
        if (!cursor_res.has_value()) {
            // Empty state trie before the very first block; cannot
            // generate a witness path until at least one account exists,
            // and the funded sender is committed in genesis so this
            // should never happen.
            std::cerr << "state-trie lookup failed at block "
                      << block_number << '\n';
            return false;
        }
        WitnessData const witness_data = generate_witness(
            db,
            cursor_res.value(),
            block_number,
            *deltas,
            read_codes,
            sds_reads);

        // Commit live; capture post-state root.
        BlockHeader const live_header{.number = block_number};
        test::commit_simple(
            tdb,
            std::move(deltas),
            code,
            bytes32_t{block_number},
            live_header);
        tdb.finalize(block_number, bytes32_t{block_number});
        tdb.set_block_and_prefix(block_number);
        bytes32_t const live_post_root = tdb.state_root();

        // ===== Witness path =====
        byte_string const witness_bytes = encode_execution_witness(
            /*block_rlp=*/{},
            witness_data.nodes,
            witness_data.codes,
            /*headers=*/{});
        auto const parsed = parse_execution_witness(witness_bytes);
        if (!parsed.has_value()) {
            std::cerr << "witness parse failed at block " << block_number
                      << ": " << parsed.error().message().c_str() << '\n';
            return false;
        }

        auto pdb_res = PartialTrieDb::from_witness(
            pre_state_root,
            parsed.value().encoded_nodes,
            parsed.value().encoded_codes);
        if (!pdb_res.has_value()) {
            std::cerr << "PartialTrieDb::from_witness failed at block "
                      << block_number << ": "
                      << pdb_res.error().message().c_str() << '\n';
            return false;
        }
        PartialTrieDb pdb = std::move(pdb_res.value());

        BlockState bs_witness{pdb, vm};
        State state_witness{bs_witness, Incarnation{block_number, 0}};
        trace::StateTracer state_tracer_witness{std::monostate{}};

        std::vector<Address> deployed_w;
        execute_iteration<traits>(
            iter,
            vm,
            bs_witness,
            state_witness,
            state_tracer_witness,
            hash_buffer,
            tx_ctx,
            chain_ctx,
            deployed_w);

        bs_witness.merge(state_witness);
        auto [deltas_w, code_w, sds_w] = std::move(bs_witness).release();

        BlockHeader const witness_header{.number = block_number};
        test::commit_simple(
            pdb,
            std::move(deltas_w),
            code_w,
            bytes32_t{block_number},
            witness_header);
        bytes32_t const witness_post_root = pdb.state_root();

        if (live_post_root != witness_post_root) {
            std::cerr << std::format(
                "STATE ROOT MISMATCH at block {}\n  live:    {}\n  "
                "witness: {}\n",
                block_number,
                fmt::format("{}", live_post_root),
                fmt::format("{}", witness_post_root));
            return false;
        }
        return true;
    }

    // Genesis: a single block-0 commit that funds SENDER. We commit via the
    // same test helper used by execute_block_test.cpp, then finalize so the
    // trie is in a state run_block() can walk.
    void commit_genesis(TrieDb &tdb)
    {
        auto deltas = test::sd();
        deltas->emplace(
            SENDER,
            StateDelta{
                .account =
                    {std::nullopt,
                     Account{
                         .balance =
                             std::numeric_limits<uint256_t>::max() / 2,
                         .nonce = 0}}});

        BlockHeader const hdr{.number = 0};
        test::commit_simple(
            tdb, std::move(deltas), Code{}, NULL_HASH_BLAKE3, hdr);
        tdb.finalize(0, NULL_HASH_BLAKE3);
        tdb.set_block_and_prefix(0);
    }

    template <Traits traits>
    void do_run(
        size_t const run_index, seed_t const seed, size_t const blocks,
        size_t const contracts, size_t const messages,
        vm::fuzzing::GeneratorFocus const &focus)
    {
        auto const rev_name = [] {
            if constexpr (is_monad_trait_v<traits>) {
                return monad_revision_to_string(traits::monad_rev());
            }
            else {
                return evmc_revision_to_string(traits::evm_rev());
            }
        }();
        std::cerr << std::format(
            "[{}] seed={} rev={}\n", run_index, seed, rev_name);

        mpt::Db db{std::make_unique<InMemoryMachine>()};
        TrieDb tdb{db};
        vm::VM vm{vm::VM::Mode::InterpreterOnly};
        random_engine_t engine{seed};

        commit_genesis(tdb);

        auto const start = std::chrono::steady_clock::now();
        size_t passed = 0;
        for (size_t i = 1; i <= blocks; ++i) {
            if (run_block<traits>(
                    engine, db, tdb, vm, i, focus, contracts, messages)) {
                ++passed;
            }
            else {
                std::cerr << "  -> stopping run after failure at block "
                          << i << '\n';
                break;
            }
        }
        auto const end = std::chrono::steady_clock::now();
        auto const ms =
            std::chrono::duration_cast<std::chrono::milliseconds>(end - start)
                .count();
        std::cerr << std::format(
            "  blocks ok: {}/{}  ({} ms)\n", passed, blocks, ms);
    }

    enum class TraitFamily
    {
        evm,
        monad,
    };

    struct Args
    {
        seed_t seed = std::numeric_limits<seed_t>::max();
        size_t runs = std::numeric_limits<size_t>::max();
        size_t blocks = 100;
        size_t contracts = 2;
        size_t messages = 4;
        TraitFamily family = TraitFamily::evm;
        evmc_revision evm_rev = EVMC_OSAKA;
        monad_revision monad_rev = MONAD_NEXT;

        void set_random_seed_if_default()
        {
            if (seed == std::numeric_limits<seed_t>::max()) {
                seed = std::random_device()();
            }
        }
    };

    Args parse_args(int const argc, char **const argv)
    {
        CLI::App app{"Monad Witness Round-Trip Fuzzer"};
        Args args{};

        app.add_option(
            "--seed",
            args.seed,
            "Seed for reproducible fuzzing (random by default)");
        app.add_option(
            "--runs",
            args.runs,
            "Number of independent runs (default: unbounded)");
        app.add_option(
            "--blocks",
            args.blocks,
            "Blocks executed per run (default 100)");
        app.add_option(
            "--contracts",
            args.contracts,
            "Contracts deployed per block (default 2)");
        app.add_option(
            "--txs-per-block",
            args.messages,
            "Messages (\"transactions\") per block (default 4)");

        std::map<std::string, TraitFamily> const family_map{
            {"evm", TraitFamily::evm},
            {"monad", TraitFamily::monad},
        };
        app.add_option(
               "--family",
               args.family,
               "Trait family to fuzz: evm or monad (default evm)")
            ->transform(CLI::CheckedTransformer(family_map, CLI::ignore_case));

        // Witness round-trip needs Cancun+ (cf. blockchain_test.cpp gating).
        std::map<std::string, evmc_revision> const evm_rev_map{
            {"CANCUN", EVMC_CANCUN},
            {"PRAGUE", EVMC_PRAGUE},
            {"OSAKA", EVMC_OSAKA},
        };
        app.add_option(
               "--evm-rev",
               args.evm_rev,
               "EVM revision (default OSAKA) — used when --family=evm")
            ->transform(CLI::CheckedTransformer(evm_rev_map, CLI::ignore_case));

        std::map<std::string, monad_revision> monad_rev_map;
        for (int i = static_cast<int>(MONAD_FOUR);
             i <= static_cast<int>(MONAD_NEXT);
             ++i) {
            monad_rev_map.emplace(
                monad_revision_to_string(static_cast<monad_revision>(i)),
                static_cast<monad_revision>(i));
        }
        app.add_option(
               "--monad-rev",
               args.monad_rev,
               "Monad revision (default MONAD_NEXT) — used when "
               "--family=monad")
            ->transform(
                CLI::CheckedTransformer(monad_rev_map, CLI::ignore_case));

        try {
            app.parse(argc, argv);
        }
        catch (CLI::ParseError const &e) {
            std::exit(app.exit(e));
        }

        args.set_random_seed_if_default();
        return args;
    }

    void dispatch_run(size_t const run_index, Args const &args)
    {
        vm::fuzzing::GeneratorFocus const focus{};
        if (args.family == TraitFamily::evm) {
            auto const rev = args.evm_rev;
            MONAD_ASSERT(rev >= EVMC_CANCUN);
            SWITCH_EVM_TRAITS(
                do_run,
                run_index,
                args.seed,
                args.blocks,
                args.contracts,
                args.messages,
                focus);
            MONAD_ABORT();
        }
        else {
            auto const rev = args.monad_rev;
            MONAD_ASSERT(rev >= MONAD_FOUR);
            SWITCH_MONAD_TRAITS(
                do_run,
                run_index,
                args.seed,
                args.blocks,
                args.contracts,
                args.messages,
                focus);
            MONAD_ABORT();
        }
    }
}

int main(int argc, char **argv)
{
    Args args = parse_args(argc, argv);
    for (size_t i = 0; i < args.runs; ++i) {
        dispatch_run(i, args);
        args.seed = random_engine_t{args.seed}();
    }
    return 0;
}
