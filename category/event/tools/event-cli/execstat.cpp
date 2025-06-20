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

#include "file.hpp"
#include "iterator.hpp"
#include "options.hpp"
#include "stats.hpp"
#include "stream.hpp"
#include "util.hpp"

#include <algorithm>
#include <chrono>
#include <cstddef>
#include <cstdint>
#include <cstdio>
#include <cstring>
#include <memory>
#include <print>
#include <span>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include <category/core/assert.h>
#include <category/core/event/event_def.h>
#include <category/execution/ethereum/core/base_ctypes.h>
#include <category/execution/ethereum/event/exec_event_ctypes.h>

using std::chrono::nanoseconds, std::chrono::system_clock;

namespace
{

constexpr uint16_t EndEventId = std::to_underlying(MONAD_EXEC_EVM_ERROR) + 1;

// There are four kinds of statistical series sampled by the execstat command:
// block series, transaction series, event series, and account series.
//
// Block series
// ---
//   A single observation per block, e.g., the amount of gas expended in each
//   block. For each variable of a block being measured, we track two
//   different block series:
//
//   1. Unadjusted - the data as it actually occurred regardless of the "size"
//      of the block
//
//   2. Transaction normalized ("txn norm") - the block observation is divided
//      by the number of transactions in the block, to normalize the data point
//      by the relative "size" of the block
//
// Transaction series
// ---
//   A single observation per transaction, e.g., the amount of gas expended in
//   each transaction. Sometimes transaction series and block series are
//   related, in that the unadjusted block series observation (e.g., total gas
//   in the block) is the sum of all the observations in the related
//   transaction series (gas used in each transaction in that block). This is
//   not always the case, e.g., the execution duration of all transactions,
//   when summed, is much larger than the block execution time, because the
//   transactions occur in parallel and their time when not being executed due
//   to stalls is still counted. The structure of the code, however, is
//   influenced by how block series are sometimes derived from transaction or
//   event series, by summing observations occurring in the scope of a block
//
// Event series
// ---
//   A single observation per event. These are used for tracking the raw number
//   of events and payload sizes for each variably-sized event type, or all
//   event types
//
// Account series
// ---
//   A single observation per account access record. This used for tracking
//   the storage key count size per access record.
//
// ## The role of block-oriented processing in statistics gathering
//
// We process statistical observations in a block-at-a-time way. For each
// block series, we'll append a single observation for that block. For the
// transaction (or event/account) series, we'll collect all new observations
// that occur in the scope of that block, and "merge" them into the statistical
// series at the end of the block.
//
// Transaction, event, and account series are modeled by a class called
// `BufferSeries`, because observations are buffered up during the scope of a
// block, before being "flushed" at the end of a block. Flushing implies
// computing the arithmetic mean incrementally, sorting the data, and running
// the TDigest::merge_sorted_points function to add the new data to the
// distribution

struct BlockSeries
{
    size_t total_observations;
    uint64_t last_unadjusted_observation;
    double last_txn_norm_observation;
    double mean;
    TDigest unadjusted_rank_stats;
    TDigest txn_norm_rank_stats;

    void set_compression(double c)
    {
        MONAD_ASSERT(total_observations == 0);
        unadjusted_rank_stats.set_compression(c);
        txn_norm_rank_stats.set_compression(c);
    }

    void add(uint64_t x, uint64_t txn_count)
    {
        last_unadjusted_observation = x;
        last_txn_norm_observation =
            txn_count > 0
                ? static_cast<double>(x) / static_cast<double>(txn_count)
                : 0.0;
        mean = (mean * static_cast<double>(total_observations) +
                static_cast<double>(x)) /
               static_cast<double>(total_observations + 1);
        ++total_observations;
        unadjusted_rank_stats.add(static_cast<double>(x));
        txn_norm_rank_stats.add(last_txn_norm_observation);
    }
};

// Transaction, event, and account series are stored in this object; because
// we buffer up all observations occurring within a block and then flush them
// at the end, these series are referred to as "buffer series"
struct BufferSeries
{
    double mean;
    std::vector<uint64_t> recent_observations;
    uint64_t recent_sum;
    size_t total_observations;
    TDigest rank_stats;

    void set_compression(double c)
    {
        MONAD_ASSERT(total_observations == 0);
        rank_stats.set_compression(c);
    }

    void append(uint64_t o)
    {
        recent_observations.push_back(o);
        recent_sum += o;
    }

    void flush()
    {
        std::ranges::sort(recent_observations);
        rank_stats.merge_sorted_points<uint64_t>(
            recent_observations, &recent_sum);
        mean =
            (mean * static_cast<double>(total_observations) +
             static_cast<double>(recent_sum)) /
            static_cast<double>(total_observations + size(recent_observations));
        total_observations += size(recent_observations);
    }

    void clear()
    {
        recent_observations.clear();
        recent_sum = 0;
    }
};

// We call a series "regular" if its block series observation is the sum
// of all the observations in an associated buffer series, e.g., the sum of all
// transaction-level gas usage observations (in some block) is also the total
// gas used in a block. `RegularSeries` is a convenience utility that
// automatically populates a BlockSeries with the sum of the BufferSeries
// observations at buffer flush time
struct RegularSeries
{
    BlockSeries block_series;
    BufferSeries buffer_series;

    void set_compression(double c)
    {
        MONAD_ASSERT(buffer_series.total_observations == 0);
        block_series.set_compression(c);
        buffer_series.set_compression(c);
    }

    void append(uint64_t o)
    {
        buffer_series.append(o);
    }

    void flush(uint64_t txn_count)
    {
        buffer_series.flush();
        block_series.add(buffer_series.recent_sum, txn_count);
    }

    void clear()
    {
        buffer_series.clear();
    }

    double last_block_observation() const
    {
        return static_cast<double>(block_series.last_unadjusted_observation);
    }

    double last_txn_norm_observation() const
    {
        return block_series.last_txn_norm_observation;
    }

    TDigest const *unadjusted_block_rank_stats() const
    {
        return &block_series.unadjusted_rank_stats;
    }

    TDigest const *txn_norm_block_rank_stats() const
    {
        return &block_series.txn_norm_rank_stats;
    }
};

struct TransactionInfo
{
    nanoseconds evm_enter_ns;
    uint64_t event_count;
    uint64_t payload_buf_usage;
    uint64_t accounts_accessed;
    uint64_t storage_slots_accessed;
    uint64_t transient_slots_accessed;
};

struct BlockInfo
{
    uint64_t start_seqno;
    uint64_t end_seqno;
    uint64_t block_number;
    monad_c_bytes32 id;
    nanoseconds epoch_start_ns;
    nanoseconds epoch_evm_enter_ns;
    nanoseconds epoch_evm_exit_ns;
    nanoseconds epoch_end_ns;
    uint64_t txn_count;
    monad_exec_event_type termination_type;
    uint64_t unscoped_account_accesses;
    std::vector<TransactionInfo> txn_info;

    void reset()
    {
        start_seqno = end_seqno = block_number = unscoped_account_accesses = 0;
        txn_info.clear();
    }
};

// All statistics gathered for a block; the series starting with `event_`
// are regular series whose associated observations are per-event, all other
// regular series are per-transaction
struct BlockStats
{
    RegularSeries event_payload_sizes[EndEventId];
    RegularSeries event_payload_buf_usage;
    BlockSeries block_txn_count;
    BlockSeries block_event_count;
    BlockSeries block_prologue_time;
    BlockSeries block_core_evm_time;
    BlockSeries block_db_time;
    BlockSeries block_total_time;
    BlockSeries block_account_access_count;
    BufferSeries txn_event_count;
    BufferSeries txn_payload_buf_usage;
    BufferSeries txn_evm_time;
    BufferSeries txn_account_access_count;
    RegularSeries log_count;
    RegularSeries call_frame_count;
    RegularSeries gas_usage;
    RegularSeries storage_access_count;
    RegularSeries transient_access_count;

    // A different kind of series than the others per account
    BufferSeries account_storage_accesses;
};

constexpr monad_exec_event_type VariablySizedEventTypes[] = {
    MONAD_EXEC_TXN_HEADER_START,
    MONAD_EXEC_TXN_ACCESS_LIST_ENTRY,
    MONAD_EXEC_TXN_LOG,
    MONAD_EXEC_TXN_CALL_FRAME,
};

struct State
{
    BlockInfo current_block;
    BlockStats stats;
    size_t num_blocks_processed;
    bool use_tty_control_codes;
};

bool on_payload_expired(
    StreamObserver *so, BlockInfo &current_block,
    monad_event_descriptor const *event, EventIterator *iter)
{
    MONAD_DEBUG_ASSERT(iter->iter_type == EventIterator::Type::EventRing);
    MappedEventRing const *const mr = iter->ring.mapped_event_ring;
    stream_warnx_f(
        so,
        "event {} payload lost! OFFSET: {}, WINDOW_START: {}",
        event->seqno,
        event->payload_buf_offset,
        mr->get_buffer_window_start());
    current_block = BlockInfo{};
    return false;
}

void set_tdigest_params(BlockStats &stats)
{
    constexpr double Compression = 1000.0;

    // Event series (regular)
    for (monad_exec_event_type const event_type : VariablySizedEventTypes) {
        stats.event_payload_sizes[event_type].set_compression(Compression);
    }
    stats.event_payload_buf_usage.set_compression(Compression);

    // Block series
    stats.block_txn_count.set_compression(Compression);
    stats.block_event_count.set_compression(Compression);
    stats.block_prologue_time.set_compression(Compression);
    stats.block_core_evm_time.set_compression(Compression);
    stats.block_db_time.set_compression(Compression);
    stats.block_total_time.set_compression(Compression);
    stats.block_account_access_count.set_compression(Compression);

    // Irregular transaction series
    stats.txn_event_count.set_compression(Compression);
    stats.txn_payload_buf_usage.set_compression(Compression);
    stats.txn_evm_time.set_compression(Compression);
    stats.txn_account_access_count.set_compression(Compression);

    // Regular transaction series
    // TODO(ken): Ethereum does not have unscoped storage accesses, but will
    //   Monad, e.g., for staking?
    stats.log_count.set_compression(Compression);
    stats.call_frame_count.set_compression(Compression);
    stats.gas_usage.set_compression(Compression);
    stats.storage_access_count.set_compression(Compression);
    stats.transient_access_count.set_compression(Compression);

    // Account series
    stats.account_storage_accesses.set_compression(Compression);
}

void flush_stats(BlockInfo const &block_info, BlockStats &stats)
{
    using std::chrono::duration_cast;

    uint64_t const txn_count = block_info.txn_count;
    for (monad_exec_event_type const event_type : VariablySizedEventTypes) {
        stats.event_payload_sizes[event_type].flush(txn_count);
    }
    stats.event_payload_buf_usage.flush(txn_count);

    stats.block_txn_count.add(txn_count, txn_count);
    stats.block_event_count.add(
        block_info.end_seqno - block_info.start_seqno + 1, txn_count);

    uint64_t const block_elapsed_prologue_time = static_cast<uint64_t>(
        (block_info.epoch_evm_enter_ns - block_info.epoch_start_ns).count());
    uint64_t const block_elapsed_core_evm_time = static_cast<uint64_t>(
        (block_info.epoch_evm_exit_ns - block_info.epoch_evm_enter_ns).count());
    uint64_t const block_elapsed_db_time = static_cast<uint64_t>(
        (block_info.epoch_end_ns - block_info.epoch_evm_exit_ns).count());
    stats.block_prologue_time.add(block_elapsed_prologue_time, txn_count);
    stats.block_core_evm_time.add(block_elapsed_core_evm_time, txn_count);
    stats.block_db_time.add(block_elapsed_db_time, txn_count);
    stats.block_total_time.add(
        block_elapsed_prologue_time + block_elapsed_core_evm_time +
            block_elapsed_db_time,
        txn_count);
    // stats.block_account_access_count is computed below, since it is the
    // computable from txn series + the unscoped accesses

    stats.txn_evm_time.flush();

    // Event counts, payload sizes, and storage access counts are nearly
    // regular: the numbers for the whole block are _almost_ the sum of all the
    // observations from the transaction-scoped events, but there are a few
    // events outside of transaction scope, so we track the transaction series
    // separately
    for (TransactionInfo const &txn_info : block_info.txn_info) {
        stats.txn_event_count.append(txn_info.event_count);
        stats.txn_payload_buf_usage.append(txn_info.payload_buf_usage);
        stats.txn_account_access_count.append(txn_info.accounts_accessed);
        stats.storage_access_count.append(txn_info.storage_slots_accessed);
        stats.transient_access_count.append(txn_info.transient_slots_accessed);
    }
    stats.txn_event_count.flush();
    stats.txn_payload_buf_usage.flush();
    stats.txn_account_access_count.flush();

    stats.block_account_access_count.add(
        stats.txn_account_access_count.recent_sum +
            block_info.unscoped_account_accesses,
        txn_count);

    stats.log_count.flush(txn_count);
    stats.call_frame_count.flush(txn_count);
    stats.gas_usage.flush(txn_count);
    stats.storage_access_count.flush(txn_count);
    stats.transient_access_count.flush(txn_count);

    stats.account_storage_accesses.flush();
}

bool process_event(
    StreamObserver *so, EventIterator *iter,
    monad_event_descriptor const *event, void const *payload, State &state)
{
    BlockInfo &current_block = state.current_block;
    BlockStats &stats = state.stats;
    auto const event_type =
        static_cast<monad_exec_event_type>(event->event_type);
    switch (event_type) {
    case MONAD_EXEC_TXN_HEADER_START:
        [[fallthrough]];
    case MONAD_EXEC_TXN_ACCESS_LIST_ENTRY:
        [[fallthrough]];
    case MONAD_EXEC_TXN_LOG:
        [[fallthrough]];
    case MONAD_EXEC_TXN_CALL_FRAME:
        stats.event_payload_sizes[event_type].append(event->payload_size);
        break;

    default:
        break;
    }

    stats.event_payload_buf_usage.append(event->payload_size);

    uint64_t const txn_id = event->content_ext[MONAD_FLOW_TXN_ID];
    bool const has_txn_info = !empty(current_block.txn_info) && txn_id != 0;
    TransactionInfo *const txn_info =
        has_txn_info ? &current_block.txn_info[txn_id - 1] : nullptr;
    if (txn_info) {
        ++txn_info->event_count;
        txn_info->payload_buf_usage += event->payload_size;
    }

    switch (event_type) {
    case MONAD_EXEC_BLOCK_START: {
        auto const *const bs =
            static_cast<monad_exec_block_start const *>(payload);
        current_block.start_seqno = event->seqno;
        current_block.id = bs->block_tag.id;
        current_block.block_number = bs->block_tag.block_number;
        current_block.txn_count = bs->eth_block_input.txn_count;
        current_block.epoch_start_ns = nanoseconds{event->record_epoch_nanos};
        current_block.txn_info.resize(current_block.txn_count);
        if (!iter->check_payload(event)) {
            return on_payload_expired(so, current_block, event, iter);
        }
    }
        return false;

    case MONAD_EXEC_BLOCK_REJECT:
    case MONAD_EXEC_TXN_REJECT:
    case MONAD_EXEC_EVM_ERROR:
        current_block.epoch_end_ns = nanoseconds{event->record_epoch_nanos};
        current_block.termination_type = event_type;
        return current_block.start_seqno != 0;

    case MONAD_EXEC_BLOCK_PERF_EVM_ENTER:
        current_block.epoch_evm_enter_ns =
            nanoseconds{event->record_epoch_nanos};
        return false;

    case MONAD_EXEC_BLOCK_PERF_EVM_EXIT:
        current_block.epoch_evm_exit_ns =
            nanoseconds{event->record_epoch_nanos};
        return false;

    case MONAD_EXEC_BLOCK_END:
        current_block.end_seqno = event->seqno;
        current_block.termination_type = event_type;
        current_block.epoch_end_ns = nanoseconds{event->record_epoch_nanos};
        if (current_block.start_seqno != 0) {
            flush_stats(current_block, stats);
            return true;
        }
        return false;

    case MONAD_EXEC_TXN_PERF_EVM_ENTER:
        if (txn_info) {
            txn_info->evm_enter_ns = nanoseconds{event->record_epoch_nanos};
        }
        return false;

    case MONAD_EXEC_TXN_PERF_EVM_EXIT:
        if (txn_info) {
            auto const evm_exit_ns = nanoseconds{event->record_epoch_nanos};
            stats.txn_evm_time.append(static_cast<uint64_t>(
                (evm_exit_ns - txn_info->evm_enter_ns).count()));
        }
        return false;

    case MONAD_EXEC_TXN_EVM_OUTPUT:
        if (txn_info) {
            monad_exec_txn_evm_output evm_output;
            std::memcpy(&evm_output, payload, sizeof evm_output);
            if (!iter->check_payload(event)) {
                return on_payload_expired(so, current_block, event, iter);
            }
            stats.log_count.append(evm_output.receipt.log_count);
            stats.call_frame_count.append(evm_output.call_frame_count);
            stats.gas_usage.append(evm_output.receipt.gas_used);
        }
        return false;

    case MONAD_EXEC_ACCOUNT_ACCESS_LIST_HEADER: {
        monad_exec_account_access_list_header h;
        std::memcpy(&h, payload, sizeof h);
        if (!iter->check_payload(event)) {
            return on_payload_expired(so, current_block, event, iter);
        }
        // This series is not exactly regular because of the prologue and
        // epilogue access lists (which are block scoped)
        if (txn_info) {
            txn_info->accounts_accessed = h.entry_count;
        }
        else {
            current_block.unscoped_account_accesses += h.entry_count;
        }
    }
        return false;

    case MONAD_EXEC_ACCOUNT_ACCESS: {
        monad_exec_account_access account_access;
        std::memcpy(&account_access, payload, sizeof account_access);
        if (!iter->check_payload(event)) {
            return on_payload_expired(so, current_block, event, iter);
        }
        if (txn_info) {
            txn_info->storage_slots_accessed +=
                account_access.storage_key_count;
            txn_info->transient_slots_accessed +=
                account_access.transient_count;
        }
        stats.account_storage_accesses.append(account_access.storage_key_count);
    }
        return false;

    default:
        return false;
    }
}

struct TDigestDescription
{
    char const *name;
    char const *unit;
    double summary;
    TDigest const *digest;
    unsigned precision;
    double scale;
};

void print_quantile_table(
    std::string_view table_name, std::span<TDigestDescription const> rows,
    std::span<double const> quantiles, std::FILE *output)
{
    std::println(
        output,
        "{:20}{:^{}}",
        "",
        table_name,
        (std::size(quantiles) + 1) * 10 + 10);
    for (TDigestDescription const &tdd : rows) {
        std::print(
            output,
            "{:>18}   {:4} {:>10.{}f}",
            tdd.name,
            tdd.unit,
            tdd.summary / tdd.scale,
            tdd.precision);
        for (double const q : quantiles) {
            std::print(
                output,
                " {:>10.{}f}",
                tdd.digest->compute_quantile(q) / tdd.scale,
                tdd.precision);
        }
        std::println(output, " {:>6}", tdd.digest->num_centroids());
    }
    std::println(output);
}

void print_block_update(State const &state, std::FILE *output)
{
    BlockInfo const &current_block = state.current_block;
    BlockStats const &stats = state.stats;
    uint64_t const txn_count = state.current_block.txn_count;
    auto const block_elapsed_nanos =
        (current_block.epoch_end_ns - current_block.epoch_start_ns).count();

    // Print some summary information about the recently observed block
    std::println(
        output,
        "BLOCK {} -- #TXN: {:>5}, GAS: {:>9}, TIME: {:>5.1f} ms, PAYLOAD_BUF: "
        "{:>9}, START_SEQNO: {}, END_SEQNO: {}",
        current_block.block_number,
        current_block.txn_count,
        stats.gas_usage.block_series.last_unadjusted_observation,
        static_cast<double>(block_elapsed_nanos) / 1000000.0,
        stats.event_payload_buf_usage.block_series.last_unadjusted_observation,
        current_block.start_seqno,
        current_block.end_seqno);

    // Print the quantile header
    constexpr double Quantiles[] = {
        0, 0.1, 0.25, 0.5, 0.75, .9, 0.95, 0.99, 0.995, 0.999, 1.0};
    constexpr unsigned QuantileColumnWidth = 10;
    std::print(output, "{:>18} | {:>4} {:>10}", "NAME", "UNIT", "SUMMARY");
    print_quantile_header(Quantiles, QuantileColumnWidth, output);
    std::println(output, " {:>6}", "#CEN");

    /*
     * Aggregate block-level stats table, unadjusted
     */

    TDigestDescription const BlockStatsTable[] = {
        {
            .name = "Transactions",
            .unit = "#",
            .summary = static_cast<double>(txn_count),
            .digest = &stats.block_txn_count.unadjusted_rank_stats,
            .precision = 1,
            .scale = 1.0,
        },
        {
            .name = "Block time (total)",
            .unit = "ms",
            .summary = static_cast<double>(
                stats.block_total_time.last_unadjusted_observation),
            .digest = &stats.block_total_time.unadjusted_rank_stats,
            .precision = 1,
            .scale = 1000000.0,
        },
        {
            .name = "Block time (pro)",
            .unit = "ms",
            .summary = static_cast<double>(
                stats.block_prologue_time.last_unadjusted_observation),
            .digest = &stats.block_prologue_time.unadjusted_rank_stats,
            .precision = 1,
            .scale = 1000000.0,
        },
        {
            .name = "Block time (EVM)",
            .unit = "ms",
            .summary = static_cast<double>(
                stats.block_core_evm_time.last_unadjusted_observation),
            .digest = &stats.block_core_evm_time.unadjusted_rank_stats,
            .precision = 1,
            .scale = 1000000.0,
        },
        {
            .name = "Block time (db)",
            .unit = "ms",
            .summary = static_cast<double>(
                stats.block_db_time.last_unadjusted_observation),
            .digest = &stats.block_db_time.unadjusted_rank_stats,
            .precision = 1,
            .scale = 1000000.0,
        },
        {.name = "Gas",
         .unit = "Mg",
         .summary = stats.gas_usage.last_block_observation(),
         .digest = stats.gas_usage.unadjusted_block_rank_stats(),
         .precision = 2,
         .scale = 1000000.0},
        {
            .name = "Events",
            .unit = "K#",
            .summary = static_cast<double>(
                stats.block_event_count.last_unadjusted_observation),
            .digest = &stats.block_event_count.unadjusted_rank_stats,
            .precision = 2,
            .scale = 1000.0,
        },
        {
            .name = "PBuf usage",
            .unit = "MiB",
            .summary = stats.event_payload_buf_usage.last_block_observation(),
            .digest = &stats.event_payload_buf_usage.block_series
                           .unadjusted_rank_stats,
            .precision = 2,
            .scale = 1 << 20,
        },
        {.name = "Logs",
         .unit = "#",
         .summary = stats.log_count.last_block_observation(),
         .digest = stats.log_count.unadjusted_block_rank_stats(),
         .precision = 1,
         .scale = 1},
        {.name = "Call frames",
         .unit = "#",
         .summary = stats.call_frame_count.last_block_observation(),
         .digest = stats.call_frame_count.unadjusted_block_rank_stats(),
         .precision = 1,
         .scale = 1},
        {.name = "Account access",
         .unit = "#",
         .summary = static_cast<double>(
             stats.block_account_access_count.last_unadjusted_observation),
         .digest = &stats.block_account_access_count.unadjusted_rank_stats,
         .precision = 1,
         .scale = 1},
        {.name = "Storage access",
         .unit = "#",
         .summary = stats.storage_access_count.last_block_observation(),
         .digest = stats.storage_access_count.unadjusted_block_rank_stats(),
         .precision = 1,
         .scale = 1}};

    print_quantile_table(
        "Block rank statistics -- summary is last observation",
        BlockStatsTable,
        Quantiles,
        output);

    /*
     * Aggregate block-level stats, normalized by transaction count
     */

    TDigestDescription const BlockNormStatsTable[] = {
        {
            .name = "Block time (total)",
            .unit = "us",
            .summary = stats.block_total_time.last_txn_norm_observation,
            .digest = &stats.block_total_time.txn_norm_rank_stats,
            .precision = 1,
            .scale = 1000.0,
        },
        {
            .name = "Gas",
            .unit = "Kg",
            .summary = stats.gas_usage.last_txn_norm_observation(),
            .digest = stats.gas_usage.txn_norm_block_rank_stats(),
            .precision = 1,
            .scale = 1000.0,
        },
        {
            .name = "Events",
            .unit = "#",
            .summary = stats.block_event_count.last_txn_norm_observation,
            .digest = &stats.block_event_count.txn_norm_rank_stats,
            .precision = 1,
            .scale = 1,
        },
        {.name = "PBuf usage",
         .unit = "KiB",
         .summary = stats.event_payload_buf_usage.last_txn_norm_observation(),
         .digest = stats.event_payload_buf_usage.txn_norm_block_rank_stats(),
         .precision = 1,
         .scale = 1 << 10},
        {.name = "Log count",
         .unit = "#",
         .summary = stats.log_count.last_txn_norm_observation(),
         .digest = stats.log_count.txn_norm_block_rank_stats(),
         .precision = 2,
         .scale = 1},
        {.name = "Call frames",
         .unit = "#",
         .summary = stats.call_frame_count.last_txn_norm_observation(),
         .digest = stats.call_frame_count.txn_norm_block_rank_stats(),
         .precision = 2,
         .scale = 1},
        {.name = "Account access",
         .unit = "#",
         .summary = stats.block_account_access_count.last_txn_norm_observation,
         .digest = &stats.block_account_access_count.txn_norm_rank_stats,
         .precision = 2,
         .scale = 1},
        {.name = "Storage access",
         .unit = "#",
         .summary = stats.storage_access_count.last_txn_norm_observation(),
         .digest = stats.storage_access_count.txn_norm_block_rank_stats(),
         .precision = 2,
         .scale = 1},
    };

    print_quantile_table(
        "Normalized block rank statistics (<stat>/#txns) -- summary is last "
        "observation",
        BlockNormStatsTable,
        Quantiles,
        output);

    /*
     * Transaction-level stats
     */

    TDigestDescription const TxnStatsTable[] = {
        {
            .name = "Txn time (EVM)",
            .unit = "ms",
            .summary = stats.txn_evm_time.mean,
            .digest = &stats.txn_evm_time.rank_stats,
            .precision = 2,
            .scale = 1000000.0,
        },
        {
            .name = "Gas",
            .unit = "Kg",
            .summary = stats.gas_usage.buffer_series.mean,
            .digest = &stats.gas_usage.buffer_series.rank_stats,
            .precision = 1,
            .scale = 1000.0,
        },
        {
            .name = "Events",
            .unit = "#",
            .summary = stats.txn_event_count.mean,
            .digest = &stats.txn_event_count.rank_stats,
            .precision = 1,
            .scale = 1,
        },
        {.name = "PBuf usage",
         .unit = "KiB",
         .summary = stats.txn_payload_buf_usage.mean,
         .digest = &stats.txn_payload_buf_usage.rank_stats,
         .precision = 2,
         .scale = 1 << 10},
        {.name = "Log count",
         .unit = "#",
         .summary = stats.log_count.buffer_series.mean,
         .digest = &stats.log_count.buffer_series.rank_stats,
         .precision = 1,
         .scale = 1},
        {.name = "Call frames",
         .unit = "#",
         .summary = stats.call_frame_count.buffer_series.mean,
         .digest = &stats.call_frame_count.buffer_series.rank_stats,
         .precision = 1,
         .scale = 1},
        {.name = "Account access",
         .unit = "#",
         .summary = stats.txn_account_access_count.mean,
         .digest = &stats.txn_account_access_count.rank_stats,
         .precision = 1,
         .scale = 1},
        {.name = "Storage access",
         .unit = "#",
         .summary = stats.storage_access_count.buffer_series.mean,
         .digest = &stats.storage_access_count.buffer_series.rank_stats,
         .precision = 1,
         .scale = 1}};

    print_quantile_table(
        "Transaction rank statistics -- summary is arithmetic mean",
        TxnStatsTable,
        Quantiles,
        output);

    /*
     * Event size statistics
     */

    TDigestDescription const EventSizeStatsTable[] = {
        {
            .name = "All event size",
            .unit = "byte",
            .summary = stats.event_payload_buf_usage.buffer_series.mean,
            .digest = &stats.event_payload_buf_usage.buffer_series.rank_stats,
            .precision = 1,
            .scale = 1.0,
        },
        {.name = "Txn start size",
         .unit = "byte",
         .summary = stats.event_payload_sizes[MONAD_EXEC_TXN_HEADER_START]
                        .buffer_series.mean,
         .digest = &stats.event_payload_sizes[MONAD_EXEC_TXN_HEADER_START]
                        .buffer_series.rank_stats,
         .precision = 1,
         .scale = 1.0},
        {.name = "Log event size",
         .unit = "byte",
         .summary =
             stats.event_payload_sizes[MONAD_EXEC_TXN_LOG].buffer_series.mean,
         .digest = &stats.event_payload_sizes[MONAD_EXEC_TXN_LOG]
                        .buffer_series.rank_stats,
         .precision = 1,
         .scale = 1.0},
        {.name = "Call frame size",
         .unit = "byte",
         .summary = stats.event_payload_sizes[MONAD_EXEC_TXN_CALL_FRAME]
                        .buffer_series.mean,
         .digest = &stats.event_payload_sizes[MONAD_EXEC_TXN_CALL_FRAME]
                        .buffer_series.rank_stats,
         .precision = 1,
         .scale = 1.0},
    };

    print_quantile_table(
        "Event size rank statistics -- summary is arithmetic mean",
        EventSizeStatsTable,
        Quantiles,
        output);

    /*
     * Account statistics
     */

    TDigestDescription const AccountStatsTable[] = {
        {
            .name = "Storage / access",
            .unit = "K/A",
            .summary = stats.account_storage_accesses.mean,
            .digest = &stats.account_storage_accesses.rank_stats,
            .precision = 1,
            .scale = 1.0,
        },
    };

    print_quantile_table(
        "Account rank statistics -- summary is arithmetic mean",
        AccountStatsTable,
        Quantiles,
        output);
}

void act_on_block_end(State &state)
{
    BlockStats &stats = state.stats;
    state.current_block.reset();
    for (RegularSeries &rs : stats.event_payload_sizes) {
        rs.clear();
    }
    stats.event_payload_buf_usage.clear();

    stats.txn_event_count.clear();
    stats.txn_payload_buf_usage.clear();
    stats.txn_evm_time.clear();
    stats.txn_account_access_count.clear();

    stats.log_count.clear();
    stats.call_frame_count.clear();
    stats.gas_usage.clear();
    stats.storage_access_count.clear();
    stats.transient_access_count.clear();

    stats.account_storage_accesses.clear();
}

std::string execstat_init(StreamObserver *so)
{
    std::unique_ptr state = std::make_unique<State>();
    state->use_tty_control_codes = use_tty_control_codes(
        so->command->get_options<ExecStatCommandOptions>()->tui_mode,
        so->command->output);
    set_tdigest_params(state->stats);
    so->state = state.release();
    return {};
}

std::string execstat_iter_init(StreamObserver *so, EventIterator *iter)
{
    return rewind_to_block_boundary(so, iter);
}

StreamUpdateResult
execstat_update(StreamObserver *so, EventIterator *iter, StreamEvent *e)
{
    if (e->iter_result == EventIteratorResult::Gap) {
        return StreamUpdateResult::Ok;
    }

    std::FILE *const out = so->command->output->file;
    State *const state = so->get_state<State>();
    if (process_event(so, iter, &e->event, e->payload, *state)) {
        ++state->num_blocks_processed;
        if (state->use_tty_control_codes) {
            if (state->num_blocks_processed == 1) {
                std::print(out, ANSI_ClearScreen);
            }
            // TODO(ken): this should just be
            //       std::print(output, "{}", ANSI_ResetCursor);
            //   which clang allows but gcc does not, bug in their
            //   consteval?
            std::print(out, "{}", ANSI_ResetCursor);
        }

        print_block_update(*state, out);
        act_on_block_end(*state);

        if (state->use_tty_control_codes) {
            std::print(out, "{}", ANSI_FinishUpdate);
        }

        std::fflush(out);
    }

    return StreamUpdateResult::Ok;
}

void execstat_finish(StreamObserver *so, StreamUpdateResult)
{
    delete so->get_state<State>();
}

} // End of anonymous namespace

StreamObserverOps const execstat_ops = {
    .init = execstat_init,
    .iter_init = execstat_iter_init,
    .update = execstat_update,
    .finish = execstat_finish,
};
