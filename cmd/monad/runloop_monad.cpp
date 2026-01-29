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

#include "runloop_monad.hpp"
#include "file_io.hpp"

#include <category/core/assert.h>
#include <category/core/blake3.hpp>
#include <category/core/bytes.hpp>
#include <category/core/config.hpp>
#include <category/core/fiber/priority_pool.hpp>
#include <category/core/keccak.hpp>
#include <category/core/procfs/statm.h>
#include <category/execution/ethereum/block_hash_buffer.hpp>
#include <category/execution/ethereum/core/block.hpp>
#include <category/execution/ethereum/core/fmt/bytes_fmt.hpp>
#include <category/execution/ethereum/core/rlp/block_rlp.hpp>
#include <category/execution/ethereum/db/db.hpp>
#include <category/execution/ethereum/db/util.hpp>
#include <category/execution/ethereum/event/exec_event_ctypes.h>
#include <category/execution/ethereum/event/exec_event_recorder.hpp>
#include <category/execution/ethereum/event/record_block_events.hpp>
#include <category/execution/ethereum/execute_block.hpp>
#include <category/execution/ethereum/execute_transaction.hpp>
#include <category/execution/ethereum/metrics/block_metrics.hpp>
#include <category/execution/ethereum/state2/block_state.hpp>
#include <category/execution/ethereum/trace/call_tracer.hpp>
#include <category/execution/ethereum/transaction_gas.hpp>
#include <category/execution/ethereum/validate_block.hpp>
#include <category/execution/ethereum/validate_transaction.hpp>
#include <category/execution/monad/chain/monad_chain.hpp>
#include <category/execution/monad/core/monad_block.hpp>
#include <category/execution/monad/core/rlp/monad_block_rlp.hpp>
#include <category/execution/monad/event/record_consensus_events.hpp>
#include <category/execution/monad/reserve_balance.hpp>
#include <category/execution/monad/validate_monad_block.hpp>
#include <category/mpt/db.hpp>
#include <category/vm/evm/switch_traits.hpp>
#include <category/vm/evm/traits.hpp>

#include <ankerl/unordered_dense.h>
#include <boost/outcome/try.hpp>
#include <quill/Quill.h>
#include <quill/detail/LogMacros.h>

#include <chrono>
#include <deque>
#include <filesystem>
#include <optional>
#include <thread>
#include <variant>
#include <vector>

MONAD_ANONYMOUS_NAMESPACE_BEGIN

struct BlockCacheEntry
{
    uint64_t block_number;
    bytes32_t parent_id;
    ankerl::unordered_dense::segmented_set<Address> senders_and_authorities;
};

using BlockCache =
    ankerl::unordered_dense::segmented_map<bytes32_t, BlockCacheEntry>;

#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wunused-variable"
#pragma GCC diagnostic ignored "-Wunused-parameter"

static ankerl::unordered_dense::segmented_set<Address>
    empty_senders_and_authorities{};

void log_tps(
    uint64_t const block_num, bytes32_t const &block_id, uint64_t const ntxs,
    uint64_t const gas, std::chrono::steady_clock::time_point const begin)
{
    auto const now = std::chrono::steady_clock::now();
    auto const elapsed = std::max(
        static_cast<uint64_t>(
            std::chrono::duration_cast<std::chrono::microseconds>(now - begin)
                .count()),
        1UL); // for the unlikely case that elapsed < 1 mic
    uint64_t const tps = (ntxs) * 1'000'000 / elapsed;
    uint64_t const gps = gas / elapsed;

    LOG_INFO(
        "Run to block= {:4d}, block_id {}, number of "
        "transactions {:6d}, "
        "tps = {:5d}, gps = {:4d} M, rss = {:6d} MB",
        block_num,
        block_id,
        ntxs,
        tps,
        gps,
        monad_procfs_self_resident() / (1L << 20));
};

#pragma GCC diagnostic pop

template <class MonadConsensusBlockHeader>
bool has_executed(
    mpt::Db const &db, MonadConsensusBlockHeader const &header,
    bytes32_t const &block_id)
{
    auto const prefix = proposal_prefix(block_id);
    return db.find(prefix, header.seqno).has_value();
}

bool validate_delayed_execution_results(
    BlockHashBuffer const &block_hash_buffer,
    std::vector<BlockHeader> const &execution_results)
{
    if (MONAD_UNLIKELY(execution_results.empty())) {
        return true;
    }

    uint64_t expected_block_number = execution_results.front().number;
    for (auto const &result : execution_results) {
        if (MONAD_UNLIKELY(expected_block_number != result.number)) {
            LOG_ERROR(
                "Validated blocks not increasing. Expected block {}, got block "
                "{}",
                expected_block_number,
                result.number);
            return false;
        }

        auto const block_hash =
            to_bytes(keccak256(rlp::encode_block_header(result)));
        if (MONAD_UNLIKELY(
                block_hash != block_hash_buffer.get(result.number))) {
            LOG_ERROR(
                "Delayed execution result mismatch for block {}",
                result.number);
            return false;
        }
        expected_block_number = result.number + 1;
    }
    return true;
}

Result<void> validate_live_execution_outputs(
    BlockHeader const &input, BlockHeader const &output)
{
    if (MONAD_UNLIKELY(input.ommers_hash != output.ommers_hash)) {
        return BlockError::WrongOmmersHash;
    }
    if (MONAD_UNLIKELY(input.transactions_root != output.transactions_root)) {
        return BlockError::WrongMerkleRoot;
    }
    if (MONAD_UNLIKELY(input.withdrawals_root != output.withdrawals_root)) {
        return BlockError::WrongMerkleRoot;
    }

    // YP eq. 56
    if (MONAD_UNLIKELY(output.gas_used > output.gas_limit)) {
        return BlockError::GasAboveLimit;
    }
    return outcome::success();
}

template <Traits traits, class MonadConsensusBlockHeader>
    requires is_monad_trait_v<traits>
Result<BlockExecOutput> propose_block(
    bytes32_t const &block_id,
    MonadConsensusBlockHeader const &consensus_header, Block block,
    BlockHashChain &block_hash_chain, MonadChain const &chain, Db &db,
    vm::VM &vm, fiber::PriorityPool &priority_pool, bool const is_first_block,
    bool const enable_tracing, BlockCache &block_cache)
{
    [[maybe_unused]] auto const block_start = std::chrono::system_clock::now();
    auto const block_begin = std::chrono::steady_clock::now();
    auto const &block_hash_buffer =
        block_hash_chain.find_chain(consensus_header.parent_id());

    // Block input validation
    BOOST_OUTCOME_TRY(static_validate_consensus_header(consensus_header));
    BOOST_OUTCOME_TRY(chain.static_validate_header(block.header));
    BOOST_OUTCOME_TRY(static_validate_block<traits>(block));

    // Sender and EIP-7702 authorities recovery
    auto const sender_recovery_begin = std::chrono::steady_clock::now();
    auto const recovered_senders =
        recover_senders(block.transactions, priority_pool);
    auto const recovered_authorities =
        recover_authorities(block.transactions, priority_pool);
    [[maybe_unused]] auto const sender_recovery_time =
        std::chrono::duration_cast<std::chrono::microseconds>(
            std::chrono::steady_clock::now() - sender_recovery_begin);
    std::vector<Address> senders(block.transactions.size());
    for (unsigned i = 0; i < recovered_senders.size(); ++i) {
        if (recovered_senders[i].has_value()) {
            senders[i] = recovered_senders[i].value();
        }
        else {
            return TransactionError::MissingSender;
        }
    }
    ankerl::unordered_dense::segmented_set<Address> senders_and_authorities;
    for (Address const &sender : senders) {
        senders_and_authorities.insert(sender);
    }
    for (std::vector<std::optional<Address>> const &authorities :
         recovered_authorities) {
        for (std::optional<Address> const &authority : authorities) {
            if (authority.has_value()) {
                senders_and_authorities.insert(authority.value());
            }
        }
    }
    MONAD_ASSERT(block_cache
                     .emplace(
                         block_id,
                         BlockCacheEntry{
                             .block_number = block.header.number,
                             .parent_id = consensus_header.parent_id(),
                             .senders_and_authorities =
                                 std::move(senders_and_authorities)})
                     .second);
    BOOST_OUTCOME_TRY(
        static_validate_monad_body<traits>(senders, block.transactions));

    // Create call frames vectors for tracers
    std::vector<std::vector<CallFrame>> call_frames{block.transactions.size()};
    std::vector<std::unique_ptr<CallTracerBase>> call_tracers{
        block.transactions.size()};
    std::vector<std::unique_ptr<trace::StateTracer>> state_tracers{
        block.transactions.size()};
    for (unsigned i = 0; i < block.transactions.size(); ++i) {
        call_tracers[i] =
            enable_tracing
                ? std::unique_ptr<CallTracerBase>{std::make_unique<CallTracer>(
                      block.transactions[i], call_frames[i])}
                : std::unique_ptr<CallTracerBase>{
                      std::make_unique<NoopCallTracer>()};
        state_tracers[i] = std::unique_ptr<trace::StateTracer>{
            std::make_unique<trace::StateTracer>(std::monostate{})};
    }

    auto const
        &[grandparent_senders_and_authorities,
          parent_senders_and_authorities] = [&] {
            if (block.header.number > 1) {
                bytes32_t const &parent_id = consensus_header.parent_id();
                MONAD_ASSERT(block_cache.contains(parent_id));
                BlockCacheEntry const &parent_entry = block_cache.at(parent_id);
                if (block.header.number > 2) {
                    bytes32_t const &grandparent_id = parent_entry.parent_id;
                    MONAD_ASSERT(block_cache.contains(grandparent_id));
                    BlockCacheEntry const &grandparent_entry =
                        block_cache.at(grandparent_id);
                    return std::tuple{
                        grandparent_entry.senders_and_authorities,
                        parent_entry.senders_and_authorities};
                }
                return std::tuple{
                    empty_senders_and_authorities,
                    parent_entry.senders_and_authorities};
            }
            return std::tuple{
                empty_senders_and_authorities, empty_senders_and_authorities};
        }();

    ChainContext<traits> const chain_context{
        .grandparent_senders_and_authorities =
            grandparent_senders_and_authorities,
        .parent_senders_and_authorities = parent_senders_and_authorities,
        .senders_and_authorities =
            block_cache.at(block_id).senders_and_authorities,
        .senders = senders,
        .authorities = recovered_authorities};

    // Core execution: transaction-level EVM execution that tracks state
    // changes but does not commit them
    db.set_block_and_prefix(
        block.header.number - 1,
        is_first_block ? bytes32_t{} : consensus_header.parent_id());
    block.header.parent_hash =
        to_bytes(keccak256(rlp::encode_block_header(db.read_eth_header())));

    BlockExecOutput exec_output;
    BlockMetrics block_metrics;
    BlockState block_state(db, vm);
    record_block_marker_event(MONAD_EXEC_BLOCK_PERF_EVM_ENTER);
    BOOST_OUTCOME_TRY(
        auto const results,
        execute_block<traits>(
            chain,
            block,
            senders,
            recovered_authorities,
            block_state,
            block_hash_buffer,
            priority_pool.fiber_group(),
            block_metrics,
            call_tracers,
            state_tracers,
            chain_context));
    record_block_marker_event(MONAD_EXEC_BLOCK_PERF_EVM_EXIT);

    // Database commit of state changes (incl. Merkle root calculations)
    block_state.log_debug();
    auto const commit_begin = std::chrono::steady_clock::now();
    block_state.commit(
        block_id,
        block.header,
        results,
        call_frames,
        senders,
        block.transactions,
        block.ommers,
        block.withdrawals);
    [[maybe_unused]] auto const commit_time =
        std::chrono::duration_cast<std::chrono::microseconds>(
            std::chrono::steady_clock::now() - commit_begin);
    if (commit_time > std::chrono::milliseconds(500)) {
        LOG_WARNING(
            "Slow block commit detected - block {}: {}",
            block.header.number,
            commit_time);
    }

    // Post-commit validation of header, with Merkle root fields filled in
    exec_output.eth_header = db.read_eth_header();
    BOOST_OUTCOME_TRY(
        validate_live_execution_outputs(block.header, exec_output.eth_header));

    // Commit prologue: computation of the Ethereum block hash to append to
    // the circular hash buffer
    exec_output.eth_block_hash =
        to_bytes(keccak256(rlp::encode_block_header(exec_output.eth_header)));
    block_hash_chain.propose(
        exec_output.eth_block_hash,
        block.header.number,
        block_id,
        consensus_header.parent_id());

    // Emit the block metrics log line
    [[maybe_unused]] auto const block_time =
        std::chrono::duration_cast<std::chrono::microseconds>(
            std::chrono::steady_clock::now() - block_begin);
    LOG_INFO(
        "__exec_block,bl={:8},id={},ts={}"
        ",tx={:5},rt={:4},rtp={:5.2f}%"
        ",ala={:3},alk={:4},alt={:>7}"
        ",sr={:>7},txe={:>8},cmt={:>8},tot={:>8},tpse={:5},tps={:5}"
        ",gas={:9},gpse={:4},gps={:3}{}{}{}",
        block.header.number,
        block_id,
        std::chrono::duration_cast<std::chrono::milliseconds>(
            block_start.time_since_epoch())
            .count(),
        block.transactions.size(),
        block_metrics.num_retries,
        100.0 * (double)block_metrics.num_retries /
            std::max(1.0, (double)block.transactions.size()),
        block_metrics.num_access_list_addrs,
        block_metrics.num_access_list_keys,
        block_metrics.access_list_time,
        sender_recovery_time,
        block_metrics.tx_exec_time,
        commit_time,
        block_time,
        block.transactions.size() * 1'000'000 /
            (uint64_t)std::max(1L, block_metrics.tx_exec_time.count()),
        block.transactions.size() * 1'000'000 /
            (uint64_t)std::max(1L, block_time.count()),
        exec_output.eth_header.gas_used,
        exec_output.eth_header.gas_used /
            (uint64_t)std::max(1L, block_metrics.tx_exec_time.count()),
        exec_output.eth_header.gas_used /
            (uint64_t)std::max(1L, block_time.count()),
        db.print_stats(),
        vm.print_and_reset_block_counts(),
        vm.print_compiler_stats());

    return exec_output;
}

template <class MonadConsensusBlockHeader, class Fn>
std::optional<bytes32_t> handle_header(
    bytes32_t const &id, byte_string_view data, uint64_t const start_exclusive,
    uint64_t const end_inclusive, Fn const &fn)
{
    auto const header_res =
        rlp::decode_consensus_block_header<MonadConsensusBlockHeader>(data);
    MONAD_ASSERT_PRINTF(
        !header_res.has_error(),
        "Could not rlp decode header: %s",
        evmc::hex(id).c_str());
    auto const &header = header_res.value();
    if (header.seqno > start_exclusive && header.seqno <= end_inclusive) {
        fn(id, header);
    }
    if (header.seqno <= (start_exclusive + 1)) {
        return std::nullopt;
    }
    return header.parent_id();
}

template <class Fn>
bytes32_t for_each_header(
    std::filesystem::path const &head, std::filesystem::path const &header_dir,
    MonadChain const &chain, uint64_t const start_exclusive,
    uint64_t const end_inclusive, Fn const &fn)
{
    bytes32_t const head_id = head_pointer_to_id(head);
    if (MONAD_UNLIKELY(head_id == bytes32_t{})) {
        return head_id;
    }
    bytes32_t id = head_id;
    while (true) {
        auto const data = read_file(id, header_dir);
        byte_string_view view{data};
        auto const ts = rlp::decode_consensus_block_header_timestamp_s(view);
        MONAD_ASSERT_PRINTF(
            !ts.has_error(),
            "Could not rlp decode timestamp from header: %s",
            evmc::hex(id).c_str());
        auto const rev = chain.get_monad_revision(ts.value());

        auto const body = [&]<Traits traits> {
            std::optional<bytes32_t> next_id;
            if constexpr (traits::monad_rev() >= MONAD_FOUR) {
                next_id = handle_header<MonadConsensusBlockHeaderV2>(
                    id, data, start_exclusive, end_inclusive, fn);
            }
            else if constexpr (traits::monad_rev() >= MONAD_THREE) {
                next_id = handle_header<MonadConsensusBlockHeaderV1>(
                    id, data, start_exclusive, end_inclusive, fn);
            }
            else {
                next_id = handle_header<MonadConsensusBlockHeaderV0>(
                    id, data, start_exclusive, end_inclusive, fn);
            }
            if (!next_id.has_value()) {
                return false;
            }
            id = next_id.value();
            return true;
        };

        auto const keep_going = [&] {
            SWITCH_MONAD_TRAITS(body.template operator());
            MONAD_ASSERT(false);
        }();

        if (!keep_going) {
            break;
        }
    }
    return head_id;
}

MONAD_ANONYMOUS_NAMESPACE_END

MONAD_NAMESPACE_BEGIN

Result<std::pair<uint64_t, uint64_t>> runloop_monad(
    MonadChain const &chain, std::filesystem::path const &ledger_dir,
    mpt::Db &raw_db, Db &db, vm::VM &vm,
    BlockHashBufferFinalized &block_hash_buffer,
    fiber::PriorityPool &priority_pool, uint64_t &finalized_block_num,
    uint64_t const end_block_num, sig_atomic_t const volatile &stop,
    bool const enable_tracing)
{
    constexpr auto SLEEP_TIME = std::chrono::microseconds(100);
    uint64_t const start_block_num = finalized_block_num;
    uint256_t const chain_id = chain.get_chain_id();
    BlockHashChain block_hash_chain(block_hash_buffer);

    auto const body_dir = ledger_dir / "bodies";
    auto const header_dir = ledger_dir / "headers";
    auto const proposed_head = header_dir / "proposed_head";
    auto const finalized_head = header_dir / "finalized_head";

    uint64_t last_finalized_block_number =
        raw_db.get_latest_finalized_version();

    MONAD_ASSERT(last_finalized_block_number != mpt::INVALID_BLOCK_NUM);

    BlockCache block_cache;
    for_each_header(
        finalized_head,
        header_dir,
        chain,
        last_finalized_block_number > 2 ? last_finalized_block_number - 2 : 0,
        last_finalized_block_number,
        [&block_cache, &priority_pool, body_dir](
            bytes32_t const &id, auto const &header) {
            MonadConsensusBlockBody const body =
                read_body(header.block_body_id, body_dir);
            std::vector<std::optional<Address>> const recovered =
                recover_senders(body.transactions, priority_pool);
            std::vector<Address> senders;
            senders.reserve(recovered.size());
            for (std::optional<Address> const &addr : recovered) {
                MONAD_ASSERT(addr.has_value());
                senders.emplace_back(addr.value());
            }
            ankerl::unordered_dense::segmented_set<Address>
                senders_and_authorities;
            for (Address const &sender : senders) {
                senders_and_authorities.insert(sender);
            }
            for (std::vector<std::optional<Address>> const &authorities :
                 recover_authorities(body.transactions, priority_pool)) {
                for (std::optional<Address> const &authority : authorities) {
                    if (authority.has_value()) {
                        senders_and_authorities.insert(authority.value());
                    }
                }
            }
            MONAD_ASSERT(block_cache
                             .emplace(
                                 id,
                                 BlockCacheEntry{
                                     .block_number = header.seqno,
                                     .parent_id = header.parent_id(),
                                     .senders_and_authorities =
                                         std::move(senders_and_authorities)})
                             .second);
        });

    uint64_t total_gas = 0;
    uint64_t ntxs = 0;

    struct ToExecute
    {
        bytes32_t block_id;
        std::variant<
            MonadConsensusBlockHeaderV0, MonadConsensusBlockHeaderV1,
            MonadConsensusBlockHeaderV2>
            header;
    };

    struct ToFinalize
    {
        uint64_t block;
        bytes32_t block_id;
        std::vector<uint64_t> verified_blocks;
    };

    std::deque<ToExecute> to_execute;
    std::deque<ToFinalize> to_finalize;

    while (finalized_block_num < end_block_num && stop == 0) {
        to_finalize.clear();
        to_execute.clear();

        last_finalized_block_number = raw_db.get_latest_finalized_version();

        // read from finalized head if we are behind
        bytes32_t const finalized_head_id = for_each_header(
            finalized_head,
            header_dir,
            chain,
            last_finalized_block_number,
            end_block_num,
            [&raw_db, &to_execute, &to_finalize](
                bytes32_t const &id, auto const &header) {
                std::vector<uint64_t> verified_blocks;
                for (BlockHeader const &h : header.delayed_execution_results) {
                    verified_blocks.push_back(h.number);
                }
                to_finalize.push_front(ToFinalize{
                    .block = header.seqno,
                    .block_id = id,
                    .verified_blocks = std::move(verified_blocks)});

                if (!has_executed(raw_db, header, id)) {
                    to_execute.push_front(
                        ToExecute{.block_id = id, .header = header});
                }
            });

        // try reading from proposal head if we are caught up
        if (to_finalize.empty()) {
            for_each_header(
                proposed_head,
                header_dir,
                chain,
                last_finalized_block_number,
                end_block_num,
                [&raw_db,
                 &to_execute,
                 &finalized_head_id,
                 &last_finalized_block_number](
                    bytes32_t const &id, auto const &header) {
                    if (MONAD_UNLIKELY(
                            header.seqno == last_finalized_block_number + 1 &&
                            finalized_head_id != header.parent_id())) {
                        // canonical chain check
                        to_execute.clear();
                    }
                    else if (!has_executed(raw_db, header, id)) {
                        to_execute.push_front(
                            ToExecute{.block_id = id, .header = header});
                    }
                });
        }

        if (MONAD_UNLIKELY(to_execute.empty() && to_finalize.empty())) {
            std::this_thread::sleep_for(SLEEP_TIME);
            continue;
        }

        auto const handle_to_execute =
            [&body_dir,
             &block_hash_chain,
             &db,
             &chain,
             &vm,
             &priority_pool,
             &last_finalized_block_number,
             chain_id,
             start_block_num,
             enable_tracing,
             &block_cache](
                bytes32_t const &block_id,
                auto const &header) -> Result<std::pair<uint64_t, uint64_t>> {
            auto const block_time_start = std::chrono::steady_clock::now();

            db.update_voted_metadata(header.seqno - 1, header.parent_id());
            record_block_qc(header, last_finalized_block_number);

            uint64_t const block_number = header.execution_inputs.number;
            auto body = read_body(header.block_body_id, body_dir);
            auto const ntxns = body.transactions.size();

            auto const &block_hash_buffer =
                block_hash_chain.find_chain(header.parent_id());

            monad_c_native_block_input monad_block_input = {};
            if constexpr (requires { header.base_fee_trend; }) {
                monad_block_input.base_fee_trend = header.base_fee_trend;
                monad_block_input.base_fee_moment = header.base_fee_moment;
            };

            record_block_start(
                block_id,
                chain_id,
                header.execution_inputs,
                block_hash_buffer.get(header.seqno - 1),
                header.block_round,
                header.epoch,
                header.timestamp_ns,
                ntxns,
                std::bit_cast<monad_c_secp256k1_pubkey>(header.author),
                monad_block_input);

            MONAD_ASSERT(validate_delayed_execution_results(
                block_hash_buffer, header.delayed_execution_results));

            auto propose_dispatch = [&]() -> Result<BlockExecOutput> {
                auto const rev =
                    chain.get_monad_revision(header.execution_inputs.timestamp);
                SWITCH_MONAD_TRAITS(
                    propose_block,
                    block_id,
                    header,
                    Block{
                        .header = header.execution_inputs,
                        .transactions = std::move(body.transactions),
                        .ommers = std::move(body.ommers),
                        .withdrawals = std::move(body.withdrawals)},
                    block_hash_chain,
                    chain,
                    db,
                    vm,
                    priority_pool,
                    block_number == start_block_num,
                    enable_tracing,
                    block_cache);
                MONAD_ABORT_PRINTF("handled rev value %d", rev);
            };
            BOOST_OUTCOME_TRY(
                BlockExecOutput const exec_output,
                record_block_result(propose_dispatch()));

            db.update_proposed_metadata(header.seqno, block_id);

            log_tps(
                block_number,
                block_id,
                ntxns,
                exec_output.eth_header.gas_used,
                block_time_start);

            return outcome::success();
        };

        for (auto const &[block_id, consensus_header] : to_execute) {
            BOOST_OUTCOME_TRY(std::visit(
                [&block_id, handle_to_execute](auto const &header) {
                    return handle_to_execute(block_id, header);
                },
                consensus_header));
        }

        for (auto const &[block, block_id, verified_blocks] : to_finalize) {
            LOG_INFO(
                "Processing finalization for block {} with block_id {}",
                block,
                block_id);
            db.finalize(block, block_id);
            block_hash_chain.finalize(block_id);
            record_block_finalized(block_id, block);
            finalized_block_num = block;

            if (!verified_blocks.empty() &&
                verified_blocks.back() != mpt::INVALID_BLOCK_NUM) {
                db.update_verified_block(verified_blocks.back());
            }
            record_block_verified(verified_blocks);
        }

        if (!to_finalize.empty()) {
            std::erase_if(
                block_cache,
                [last_finalized = to_finalize.back().block](
                    std::pair<bytes32_t, BlockCacheEntry> const &entry) {
                    return last_finalized > 1 &&
                           entry.second.block_number < last_finalized - 1;
                });
        }
    }

    return {ntxs, total_gas};
}

MONAD_NAMESPACE_END
