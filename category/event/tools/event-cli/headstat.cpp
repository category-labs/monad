#include "command.hpp"
#include "file.hpp"
#include "options.hpp"
#include "stats.hpp"
#include "util.hpp"

#include <algorithm>
#include <chrono>
#include <cstddef>
#include <cstdint>
#include <cstdio>
#include <iterator>
#include <list>
#include <print>
#include <span>
#include <utility>
#include <vector>

#include <signal.h>
#include <time.h>

#include <category/core/assert.h>
#include <category/core/event/event_ring.h>

using std::chrono::duration_cast, std::chrono::nanoseconds,
    std::chrono::system_clock, std::chrono::seconds;

extern sig_atomic_t g_should_exit;

namespace
{

struct RankStatistics
{
    std::vector<double> sample;
    TDigest t_digest;
};

struct EventRingControlData
{
    system_clock::time_point time;
    uint64_t last_seqno;
    uint64_t next_payload_buf;
};

struct EventRingState
{
    MappedEventRing *ring;
    std::vector<EventRingControlData> control_sample;
    std::pair<uint64_t, uint64_t> last_seqno_range;
    RankStatistics event_rate;
    RankStatistics payload_buf_alloc_rate;
    RankStatistics avg_payload_size;
};

constexpr size_t ControlSampleSize = 128;
constexpr nanoseconds ControlSamplePeriod =
    std::chrono::duration_cast<nanoseconds>(seconds{1}) / ControlSampleSize;

std::vector<MappedEventRing *> create_samples(std::list<EventRingState> &states)
{
    std::vector<MappedEventRing *> finalized_rings;

    while (g_should_exit == 0 && !empty(states) &&
           size(states.front().control_sample) < ControlSampleSize) {
        auto i_state = begin(states);
        auto const i_end_state = end(states);

        auto const start_time = system_clock::now();
        while (i_state != i_end_state) {
            // Remember the current state, and advance `i_state` past it; we do
            // this to safely erase defunct event ring states from the list
            // without disturbing the loop iteration
            auto const i_current = i_state++;

            // Add a single data point to the control sample
            EventRingState &state = *i_current;
            monad_event_ring_header const *const h = state.ring->get_header();
            EventRingControlData const &last =
                state.control_sample.emplace_back(
                    system_clock::now(),
                    __atomic_load_n(&h->control.last_seqno, __ATOMIC_ACQUIRE),
                    __atomic_load_n(
                        &h->control.next_payload_byte, __ATOMIC_ACQUIRE));

            auto const i_prev = ++state.control_sample.rbegin();
            if (i_prev == state.control_sample.rend()) {
                // The sample has only one observation
                continue;
            }
            // The sample has more than one observation, check if zero events
            // were produced in this tick period and if so, further check if
            // the event ring is abandoned. If so, destroy its state
            EventRingControlData const &prev = *i_prev;
            if (last.last_seqno - prev.last_seqno == 0 &&
                state.ring->is_finalized()) {
                finalized_rings.push_back(state.ring);
                states.erase(i_current);
            }
        }

        // Sleep until it's time to gather another datapoint in the statistical
        // sample; although we would prefer std::this_thread::sleep_until here,
        // we need the sleep to be interruptable, so need nanosleep(2) here
        auto const sleep_ns = duration_cast<nanoseconds>(
            start_time + ControlSamplePeriod - system_clock::now());
        if (sleep_ns.count() > 0) {
            // nanosleep(2) needs the seconds and nanoseconds broken down,
            // otherwise it returns EINVAL
            seconds const sleep_s = std::chrono::floor<seconds>(sleep_ns);
            timespec const sleep_time = {
                .tv_sec = sleep_s.count(),
                .tv_nsec = (sleep_ns - sleep_s).count()};
            // If we wake up with EINTR, g_should_exit will be set, so we'll
            // fall through and print one last update
            // TODO(ken): EINTR wakeup only works if it's a thread-directed
            //   signal to this thread, which it won't be; what to do about
            //   this?
            (void)nanosleep(&sleep_time, nullptr);
        }
    }

    return finalized_rings;
}

void compute_rank_stats(EventRingState &state, bool discard_zero_samples)
{
    state.event_rate.sample.clear();
    state.payload_buf_alloc_rate.sample.clear();
    state.avg_payload_size.sample.clear();

    // Turn the ring control sample into rate-per-second sample data, e.g.,
    //
    //   (wr_seqno_{i} - wr_seqno_{i-1}) / (time_{i} - time_{i-1})
    //
    // Also compute the average payload sample
    auto i_prev = begin(state.control_sample);
    auto const i_end = end(state.control_sample);
    for (auto i = next(i_prev); i != i_end; ++i, ++i_prev) {
        double const elapsed_seconds =
            static_cast<double>((i->time - i_prev->time).count()) /
            system_clock::duration::period::den;

        double const new_event_count =
            static_cast<double>(i->last_seqno - i_prev->last_seqno);
        if (discard_zero_samples && new_event_count == 0) {
            continue;
        }

        double const new_payload_byte_count =
            static_cast<double>(i->next_payload_buf - i_prev->next_payload_buf);
        if (discard_zero_samples && new_payload_byte_count == 0) {
            continue;
        }

        double const avg_payload_size =
            new_event_count > 0 ? new_payload_byte_count / new_event_count : 0;

        state.event_rate.sample.push_back(new_event_count / elapsed_seconds);
        state.payload_buf_alloc_rate.sample.push_back(
            new_payload_byte_count / elapsed_seconds);
        state.avg_payload_size.sample.push_back(avg_payload_size);
    }

    // The only purpose of the control sample is to compute the derived sample;
    // clear the vector to reuse it next time, but save the seqno sample seqno
    // ranges, printed for debugging's sake
    state.last_seqno_range = {
        state.control_sample.front().last_seqno,
        state.control_sample.back().last_seqno};
    state.control_sample.clear();

    for (RankStatistics *r :
         {&state.event_rate,
          &state.payload_buf_alloc_rate,
          &state.avg_payload_size}) {
        std::ranges::sort(r->sample);
        r->t_digest.merge_sorted_points<double>(r->sample, nullptr);
    }
}

void print_update(EventRingState const &state, std::FILE *output)
{
    struct StatDescription
    {
        std::string_view name;
        std::string_view unit;
        double divisor;
        RankStatistics const *stats;
    } const StatsTable[] = {
        {.name = "Event rate",
         .unit = "Kev/s",
         .divisor = 1000,
         .stats = &state.event_rate},
        {.name = "Payload alloc",
         .unit = "MiB/s",
         .divisor = (1 << 20),
         .stats = &state.payload_buf_alloc_rate},
        {.name = "Avg. payload",
         .unit = "bytes",
         .divisor = 1,
         .stats = &state.avg_payload_size},
    };

    std::println(
        output,
        "stats for {} -- seqno range [{}, {}]",
        state.ring->describe(),
        state.last_seqno_range.first,
        state.last_seqno_range.second);
    // Format is
    // --            UNIT   <QUANTILES>
    // <stat name>   <un>
    //   Recent             <recent quantile data>
    //   T-Digest           <t-digest quantile estimates>
    double const quantiles[] = {
        0, 0.1, 0.25, 0.5, 0.75, .9, 0.95, 0.99, 0.999, 1.0};
    std::print(output, "{:16} {:>4}", "--", "UNIT");
    print_quantile_header(quantiles, 8, output);
    std::println(output, " {:>8}", "#CEN");
    for (StatDescription const &sd : StatsTable) {
        std::println(output, "{:16} {}", sd.name, sd.unit);

        // Print recent
        std::print(output, "{:21}", "  Recent");
        for (double const q : quantiles) {
            std::print(
                output,
                " {:8.1f}",
                compute_quantile_sorted(sd.stats->sample, q) / sd.divisor);
        }
        std::println(output, " {:>8}", "N/A");

        // Print t-digest
        std::print(output, "{:21}", "  T-Digest");
        for (double const q : quantiles) {
            std::print(
                output,
                " {:>8.1f}",
                sd.stats->t_digest.compute_quantile(q) / sd.divisor);
        }
        std::println(output, " {:>8}", sd.stats->t_digest.num_centroids());
    }
}

} // End of anonymous namespace

void headstat_thread_main(Command const *const command)
{
    std::list<EventRingState> states;
    auto const *const options = command->get_options<HeadStatCommandOptions>();

    for (EventSourceSpec const &ess : command->event_sources) {
        if (ess.source_file->get_type() != EventSourceFile::Type::EventRing ||
            static_cast<MappedEventRing *>(ess.source_file)
                    ->get_initial_liveness() == EventRingLiveness::Snapshot) {
            continue;
        }
        EventRingState &s = states.emplace_back(
            static_cast<MappedEventRing *>(ess.source_file));
        s.control_sample.reserve(ControlSampleSize);

        constexpr double DefaultCompression = 1000.0;
        for (RankStatistics *r :
             {&s.event_rate, &s.payload_buf_alloc_rate, &s.avg_payload_size}) {
            r->t_digest.set_compression(DefaultCompression);
        }
    }

    uint32_t const print_threshold = options->stats_interval;
    uint32_t n_samples_in_print_threshold = 0;
    size_t num_total_samples = 0;
    std::FILE *const out = command->output->file;
    bool const tty_control_codes =
        use_tty_control_codes(options->tui_mode, command->output);

    while (g_should_exit == 0 && !empty(states)) {
        ++num_total_samples;

        // Take a statistical sample for each event ring. A sample contains
        // `SampleSize` observations and takes about 1 second to gather (the
        // sampling rate is approximately `SampleSize` Hertz). If any event
        // rings become finalized (no longer written to), they are removed from
        // the state list and returned to us.
        std::vector<MappedEventRing *> const finalized_rings =
            create_samples(states);

        if (tty_control_codes) {
            if (num_total_samples == 1) {
                std::print(out, ANSI_ClearScreen);
            }
            std::print(out, "{}", ANSI_ResetCursor);
        }

        (void)num_total_samples; // XXX: display this later?
        for (MappedEventRing const *const mr : finalized_rings) {
            std::println(
                out, "no more writers for event ring {}", mr->describe());
        }

        for (EventRingState &s : states) {
            compute_rank_stats(s, options->discard_zero_samples);
        }
        if (++n_samples_in_print_threshold == print_threshold) {
            // We've accumulated the number of samples needed to print a
            // statistics line
            for (EventRingState const &s : states) {
                print_update(s, out);
            }
            n_samples_in_print_threshold = 0;
            if (tty_control_codes) {
                std::print(out, "{}", ANSI_FinishUpdate);
            }
        }
    }
}
