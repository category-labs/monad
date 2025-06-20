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

#include "command.hpp"
#include "file.hpp"
#include "iterator.hpp"
#include "options.hpp"
#include "stats.hpp"
#include "stream.hpp"
#include "util.hpp"

#include <algorithm>
#include <chrono>
#include <csignal>
#include <cstddef>
#include <cstdint>
#include <cstdio>
#include <cstring>
#include <deque>
#include <iterator>
#include <memory>
#include <optional>
#include <print>
#include <ranges>
#include <ratio>
#include <span>
#include <string>
#include <string_view>
#include <vector>

#include <category/core/assert.h>
#include <category/core/event/event_def.h>
#include <category/execution/ethereum/core/base_ctypes.h>
#include <category/execution/ethereum/event/exec_event_ctypes.h>

using std::chrono::nanoseconds, std::chrono::system_clock;

extern sig_atomic_t g_should_exit;

namespace
{

struct OutlierParams
{
    unsigned table_size;
    unsigned min_tx;
};

// Information about a single block gathered between BLOCK_START and a
// terminating block event (usually BLOCK_END)
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
    nanoseconds prologue_duration_ns;
    nanoseconds core_evm_duration_ns;
    nanoseconds db_duration_ns;
    nanoseconds total_duration_ns;
    uint64_t txn_count;
    uint64_t gas_used;
    monad_exec_event_type termination_type;

    double txn_normalized_time() const
    {
        return static_cast<double>(total_duration_ns.count()) /
               static_cast<double>(std::max<uint64_t>(txn_count, 1));
    }

    double gas_efficiency() const
    {
        return static_cast<double>(gas_used) /
               static_cast<double>(total_duration_ns.count());
    }
};

// A unit/second rate, but measured with samples of "seconds" referring to
// different scales, namely:
//
//   1. wall_rate - unit per wall clock time
//   2. block_rate - unit per block seconds elapsed (i.e., elapsed time only
//        between BLOCK_START and BLOCK_END; other time ignored)
//   3. evm_rate - unit per EVM execution time (i.e., within execute_block)
struct SampleRate
{
    uint64_t sample_weight;
    double wall_rate;
    double block_rate;
    double evm_rate;
};

struct TxnSample
{
    uint64_t block_count;
    SampleRate tps;
    SampleRate gps;
};

struct State
{
    std::vector<BlockInfo> current_aggregate;
    nanoseconds aggregate_evm_elapsed;
    system_clock::time_point wall_start;
    std::deque<TxnSample> samples;
    uint64_t total_blocks_processed;
    uint64_t total_txn_count;
    uint64_t total_gas_used;
    std::vector<BlockInfo> long_txn_time_outliers;
    std::vector<BlockInfo> gas_efficiency_outliers;
    OutlierParams long_txn_time_params;
    OutlierParams gas_efficiency_params;
    BlockStatCommandOptions const *options;
};

bool on_payload_expired(
    monad_event_descriptor const *event, EventIterator *iter, std::FILE *out)
{
    MONAD_DEBUG_ASSERT(iter->iter_type == EventIterator::Type::EventRing);
    MappedEventRing const *const mr = iter->ring.mapped_event_ring;
    std::println(
        out,
        "ERROR: event {} payload lost! OFFSET: {}, WINDOW_START: {}",
        event->seqno,
        event->payload_buf_offset,
        mr->get_buffer_window_start());
    return false;
}

bool process_event(
    EventIterator *iter, monad_event_descriptor const *event,
    void const *payload, BlockInfo &block_info)
{
    auto const event_type =
        static_cast<monad_exec_event_type>(event->event_type);

    switch (event_type) {
    case MONAD_EXEC_BLOCK_START: {
        auto const *const bs =
            static_cast<monad_exec_block_start const *>(payload);
        block_info.start_seqno = event->seqno;
        block_info.id = bs->block_tag.id;
        block_info.block_number = bs->block_tag.block_number;
        block_info.txn_count = bs->eth_block_input.txn_count;
        block_info.epoch_start_ns = nanoseconds{event->record_epoch_nanos};
        if (!iter->check_payload(event)) {
            return on_payload_expired(event, iter, stderr);
        }
    }
        return false;

    case MONAD_EXEC_BLOCK_REJECT:
    case MONAD_EXEC_TXN_REJECT:
    case MONAD_EXEC_EVM_ERROR:
        block_info.epoch_end_ns = nanoseconds{event->record_epoch_nanos};
        block_info.termination_type = event_type;
        return block_info.start_seqno != 0;

    case MONAD_EXEC_BLOCK_PERF_EVM_ENTER:
        block_info.epoch_evm_enter_ns = nanoseconds{event->record_epoch_nanos};
        block_info.prologue_duration_ns =
            block_info.epoch_evm_enter_ns - block_info.epoch_start_ns;
        return false;

    case MONAD_EXEC_BLOCK_PERF_EVM_EXIT:
        block_info.epoch_evm_exit_ns = nanoseconds{event->record_epoch_nanos};
        block_info.core_evm_duration_ns =
            block_info.epoch_evm_exit_ns - block_info.epoch_evm_enter_ns;
        return false;

    case MONAD_EXEC_TXN_EVM_OUTPUT:
        if (block_info.block_number > 0) {
            monad_exec_txn_evm_output evm_output;
            std::memcpy(&evm_output, payload, sizeof evm_output);
            if (!iter->check_payload(event)) {
                return on_payload_expired(event, iter, stderr);
            }
            block_info.gas_used += evm_output.receipt.gas_used;
        }
        return false;

    case MONAD_EXEC_BLOCK_END:
        if (block_info.start_seqno == 0) {
            return false;
        }
        block_info.end_seqno = event->seqno;
        block_info.termination_type = event_type;
        block_info.epoch_end_ns = nanoseconds{event->record_epoch_nanos};
        block_info.db_duration_ns =
            block_info.epoch_end_ns - block_info.epoch_evm_exit_ns;
        block_info.total_duration_ns =
            block_info.epoch_end_ns - block_info.epoch_start_ns;
        return true;

    default:
        return false;
    }
}

void print_block_update(BlockInfo const &block_info, std::FILE *output)
{
    using std::chrono::duration_cast, std::chrono::milliseconds,
        std::chrono::microseconds;

    double const gas_used = static_cast<double>(block_info.gas_used);

    auto const compute_gpus = [gas_used](nanoseconds elapsed) {
        auto const time_us =
            static_cast<double>(duration_cast<microseconds>(elapsed).count());
        return gas_used / time_us;
    };

    std::println(
        output,
        "BLK: {:9}  #TX: {:4}  GAS: {:6.1f}M  TIME: {:5}  P: {:4}  E: {:5}  "
        "D: {:4}  NORM_TX: {:6.1f}us  GPUS: {:6.1f}  GPUS-E: {:7.1f}",
        block_info.block_number,
        block_info.txn_count,
        gas_used / 1'000'000.0,
        duration_cast<milliseconds>(block_info.total_duration_ns),
        duration_cast<milliseconds>(block_info.prologue_duration_ns),
        duration_cast<milliseconds>(block_info.core_evm_duration_ns),
        duration_cast<milliseconds>(block_info.db_duration_ns),
        block_info.txn_normalized_time() / 1000,
        compute_gpus(block_info.total_duration_ns),
        compute_gpus(block_info.core_evm_duration_ns));
}

void check_long_txn_time_outlier(
    BlockInfo const block_info, OutlierParams const &params,
    std::vector<BlockInfo> &long_txn_time_outliers)
{
    if (block_info.txn_count < params.min_tx || params.table_size == 0) {
        return;
    }
    if (size(long_txn_time_outliers) == params.table_size &&
        long_txn_time_outliers.front().txn_normalized_time() >=
            block_info.txn_normalized_time()) {
        return;
    }

    if (size(long_txn_time_outliers) < params.table_size) {
        long_txn_time_outliers.push_back(block_info);
    }
    else {
        long_txn_time_outliers.front() = block_info;
    }
    double const partial_sort_value = block_info.txn_normalized_time();
    std::ranges::stable_partition(
        long_txn_time_outliers,
        [partial_sort_value](double t) { return t < partial_sort_value; },
        &BlockInfo::txn_normalized_time);
}

void check_gas_efficiency_outlier(
    BlockInfo const block_info, OutlierParams const &params,
    std::vector<BlockInfo> &gas_efficiency_outliers)
{
    if (block_info.txn_count < params.min_tx || params.table_size == 0) {
        return;
    }
    if (size(gas_efficiency_outliers) == params.table_size &&
        gas_efficiency_outliers.back().gas_efficiency() <=
            block_info.gas_efficiency()) {
        return;
    }

    if (size(gas_efficiency_outliers) < params.table_size) {
        gas_efficiency_outliers.push_back(block_info);
    }
    else {
        gas_efficiency_outliers.back() = block_info;
    }
    double const partial_sort_value = block_info.gas_efficiency();
    std::ranges::stable_partition(
        gas_efficiency_outliers,
        [partial_sort_value](double e) { return e <= partial_sort_value; },
        &BlockInfo::gas_efficiency);
}

void create_aggregate_sample(State &state, std::optional<double> wall_seconds)
{
    struct AggregateBlockInfo
    {
        double prologue_seconds;
        double core_evm_seconds;
        double db_seconds;
        double wall_seconds;
        uint64_t gas_used;
        uint64_t txn_count;

        double total_block_seconds() const
        {
            return prologue_seconds + core_evm_seconds + db_seconds;
        }
    };

    AggregateBlockInfo abi{};
    for (BlockInfo const &bi : state.current_aggregate) {
        constexpr double ns_per_sec = 1'000'000'000.0;
        abi.prologue_seconds +=
            static_cast<double>(bi.prologue_duration_ns.count()) / ns_per_sec;
        abi.core_evm_seconds +=
            static_cast<double>(bi.core_evm_duration_ns.count()) / ns_per_sec;
        abi.db_seconds +=
            static_cast<double>(bi.db_duration_ns.count()) / ns_per_sec;
        abi.gas_used += bi.gas_used;
        abi.txn_count += bi.txn_count;
    }
    if (state.wall_start == system_clock::time_point{} || !wall_seconds) {
        // When interactive, this will be skewed the first time because we'll
        // start in the middle of the block, lengthening the apparent time of
        // the first block. In the capture file replay case, the wall time
        // measurement is not accurate at all, so we just duplicate the block
        // time series.
        abi.wall_seconds = abi.total_block_seconds();
    }
    else {
        abi.wall_seconds = *wall_seconds;
    }

    auto const make_rate = [](uint64_t v, double s) -> double {
        return static_cast<double>(v) / s;
    };

    auto const make_scaled_rate =
        []<intmax_t N, intmax_t D>(
            uint64_t v, std::ratio<N, D> const, double s) -> double {
        return static_cast<double>(v) / (s * N);
    };

    TxnSample &sample = state.samples.emplace_back();
    sample.block_count = state.current_aggregate.size();

    sample.tps.sample_weight = abi.txn_count;
    sample.tps.wall_rate = make_rate(abi.txn_count, abi.wall_seconds);
    sample.tps.block_rate = make_rate(abi.txn_count, abi.total_block_seconds());
    sample.tps.evm_rate = make_rate(abi.txn_count, abi.core_evm_seconds);

    sample.gps.sample_weight = abi.gas_used;
    sample.gps.wall_rate =
        make_scaled_rate(abi.gas_used, std::mega{}, abi.wall_seconds);
    sample.gps.block_rate =
        make_scaled_rate(abi.gas_used, std::mega{}, abi.total_block_seconds());
    sample.gps.evm_rate =
        make_scaled_rate(abi.gas_used, std::mega{}, abi.core_evm_seconds);

    state.total_txn_count += abi.txn_count;
    state.total_gas_used += abi.gas_used;

    state.aggregate_evm_elapsed = {};
    state.current_aggregate.clear();
    state.current_aggregate.emplace_back();
}

bool act_on_block_end(State &state, bool accurate_wall_time)
{
    using std::chrono::seconds;
    constexpr seconds sample_time{1};

    auto const now = system_clock::now();
    std::optional<double> const opt_wall_seconds =
        accurate_wall_time
            ? std::
                  optional{static_cast<double>((now - state.wall_start).count()) / 1'000'000'000.0}
            : std::nullopt;

    if (state.current_aggregate.back().gas_used > 0) {
        check_long_txn_time_outlier(
            state.current_aggregate.back(),
            state.long_txn_time_params,
            state.long_txn_time_outliers);
        check_gas_efficiency_outlier(
            state.current_aggregate.back(),
            state.gas_efficiency_params,
            state.gas_efficiency_outliers);
    }

    state.aggregate_evm_elapsed +=
        state.current_aggregate.back().core_evm_duration_ns;
    if (duration_cast<seconds>(state.aggregate_evm_elapsed) < sample_time) {
        state.current_aggregate.emplace_back();
        return false;
    }

    create_aggregate_sample(state, opt_wall_seconds);
    state.wall_start = now;
    return true;
}

void print_txn_sample(TxnSample const &sample, std::FILE *output)
{
    std::println(
        output,
        "#BLK: {:2}  #TX: {:5}  TPS-W: {:5.1f}  "
        "TPS-B: {:5.1f}  TPS-E: {:7.1f}  GAS: {:6.1f}M  "
        "GPS-W: {:5.1f}M  GPS-B: {:5.1f}M  GPS-E: {:6.1f}M",
        sample.block_count,
        sample.tps.sample_weight,
        sample.tps.wall_rate,
        sample.tps.block_rate,
        sample.tps.evm_rate,
        static_cast<double>(sample.gps.sample_weight) / 1'000'000.0,
        sample.gps.wall_rate,
        sample.gps.block_rate,
        sample.gps.evm_rate);
}

struct RateSeries
{
    std::vector<double> sample_weights;
    std::vector<double> wall_series;
    std::vector<double> block_series;
    std::vector<double> evm_series;

    static RateSeries create(
        std::deque<TxnSample> const &samples, uint64_t total_sample_weight,
        SampleRate const(TxnSample::*const extract))
    {
        RateSeries rs;
        size_t const sample_count = size(samples);
        for (std::vector<double> *v :
             {&rs.sample_weights,
              &rs.wall_series,
              &rs.block_series,
              &rs.evm_series}) {
            v->reserve(sample_count);
        }
        for (TxnSample const &sample : samples) {
            SampleRate const &r = sample.*extract;
            rs.sample_weights.emplace_back(
                static_cast<double>(r.sample_weight) /
                static_cast<double>(total_sample_weight));
            rs.wall_series.emplace_back(r.wall_rate);
            rs.block_series.emplace_back(r.block_rate);
            rs.evm_series.emplace_back(r.evm_rate);
        }
        return rs;
    }
};

double
compute_mean(std::span<double const> weights, std::span<double const> values)
{
    double mean = 0;
    for (auto [w, v] : std::views::zip(weights, values)) {
        mean += w * v;
    }
    return mean;
}

void print_quantile_table(
    std::string_view table_name, RateSeries rate_series,
    std::span<double const> quantiles, std::FILE *output)
{
    std::println(
        output,
        "{:20}{:^{}}",
        "",
        table_name,
        (std::size(quantiles) + 1) * 10 + 10);

    struct SeriesDescriptionEntry
    {
        char const *name;
        std::span<double> values;
    } const Descriptions[] = {
        {.name = "Wall time", .values = rate_series.wall_series},
        {.name = "Block time", .values = rate_series.block_series},
        {.name = "EVM time", .values = rate_series.evm_series},
    };

    for (SeriesDescriptionEntry const &sde : Descriptions) {
        std::print(
            output,
            "{:>10}   {:>8.1f}",
            sde.name,
            compute_mean(rate_series.sample_weights, sde.values));
        std::ranges::sort(sde.values);
        for (double const q : quantiles) {
            std::print(
                output, " {:>10.1f}", compute_quantile_sorted(sde.values, q));
        }
        std::println(output);
    }
    std::println(output);
}

void compute_final_stats(
    std::deque<TxnSample> const &samples, uint64_t total_txn_count,
    uint64_t total_gas_used, std::FILE *output)
{
    // Print the quantile header
    constexpr double Quantiles[] = {0, 0.1, 0.25, 0.5, 0.75, .9, 1.0};
    constexpr unsigned QuantileColumnWidth = 10;
    std::print(output, "{:>10}   {:>8}", "NAME", "AVG");
    print_quantile_header(Quantiles, QuantileColumnWidth, output);
    std::println(output);

    print_quantile_table(
        "Transactions per second (TPS)",
        RateSeries::create(samples, total_txn_count, &TxnSample::tps),
        Quantiles,
        output);

    print_quantile_table(
        "Gas per second (GPS)",
        RateSeries::create(samples, total_gas_used, &TxnSample::gps),
        Quantiles,
        output);
}

std::string blockstat_init(StreamObserver *so)
{
    std::unique_ptr state = std::make_unique<State>();
    BlockStatCommandOptions const *const options = state->options =
        so->command->get_options<BlockStatCommandOptions>();

    if (options->outlier_size) {
        state->long_txn_time_outliers.reserve(*options->outlier_size + 1);
        state->gas_efficiency_outliers.reserve(*options->outlier_size + 1);

        state->long_txn_time_params.table_size = *options->outlier_size;
        state->long_txn_time_params.min_tx =
            options->long_txn_time_min_txn.value_or(1);

        state->gas_efficiency_params.table_size = *options->outlier_size;
        state->gas_efficiency_params.min_tx =
            options->gas_efficiency_min_txn.value_or(0);
    }

    state->current_aggregate.emplace_back();
    so->state = state.release();
    return {};
}

std::string blockstat_iter_init(StreamObserver *so, EventIterator *iter)
{
    return rewind_to_block_boundary(so, iter);
}

StreamUpdateResult
blockstat_update(StreamObserver *so, EventIterator *iter, StreamEvent *e)
{
    if (e->iter_result == EventIteratorResult::Gap) {
        return StreamUpdateResult::Ok;
    }

    MONAD_ASSERT(e->iter_result == EventIteratorResult::Success);
    State *const state = so->get_state<State>();
    if (process_event(
            iter, &e->event, e->payload, state->current_aggregate.back())) {
        std::FILE *const out = so->command->output->file;
        ++state->total_blocks_processed;

        if (state->options->display_blocks) {
            print_block_update(state->current_aggregate.back(), out);
            std::fflush(out);
        }
        if (act_on_block_end(
                *state, so->get_event_source().source_file->is_interactive())) {
            print_txn_sample(state->samples.back(), out);
        }
        std::fflush(out);
    }

    return StreamUpdateResult::Ok;
}

void blockstat_finish(StreamObserver *so, StreamUpdateResult)
{
    State *const state = so->get_state<State>();
    Command *const command = so->command;
    std::FILE *const out = command->output->file;

    if (!empty(state->current_aggregate)) {
        // Flush the final sample
        auto const now = system_clock::now();
        std::optional<double> const opt_wall_seconds =
            so->get_event_source().source_file->is_interactive()
                ? std::
                      optional{static_cast<double>((now - state->wall_start).count()) / 1'000'000'000.0}
                : std::nullopt;
        create_aggregate_sample(*state, opt_wall_seconds);
        if (g_should_exit) {
            std::println(out); // Skip line because ^C echoed
        }
        print_txn_sample(state->samples.back(), out);
    }

    if (!empty(state->samples)) {
        std::println(
            out,
            "\n{} transactions, {}M gas in {} blocks ({} rate samples)",
            state->total_txn_count,
            state->total_gas_used / 1'000'000,
            state->total_blocks_processed,
            size(state->samples));
        compute_final_stats(
            state->samples, state->total_txn_count, state->total_gas_used, out);
    }

    if (state->options->outlier_size) {
        std::println("Transaction-normalized block time outliers:");
        for (BlockInfo const &bi : state->long_txn_time_outliers) {
            print_block_update(bi, out);
        }
        std::println("Gas efficiency outliers:");
        for (BlockInfo const &bi : state->gas_efficiency_outliers) {
            print_block_update(bi, out);
        }
    }

    delete state;
}

} // End of anonymous namespace

StreamObserverOps const blockstat_ops = {
    .init = blockstat_init,
    .iter_init = blockstat_iter_init,
    .update = blockstat_update,
    .finish = blockstat_finish,
};
