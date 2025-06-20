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

#include "stream.hpp"
#include "command.hpp"
#include "err_cxx.hpp"
#include "file.hpp"
#include "iterator.hpp"
#include "util.hpp"

#include <cstddef>
#include <list>
#include <optional>
#include <span>
#include <string>

#include <signal.h>
#include <stdio.h>
#include <sysexits.h>

#include <category/core/assert.h>
#include <category/core/event/event_def.h>
#include <category/execution/ethereum/event/exec_event_ctypes.h>
#include <category/execution/ethereum/event/exec_iter_help.h>

extern sig_atomic_t g_should_exit;

namespace
{

struct StreamObserverState
{
    EventIterator iter;
    StreamEvent stream_event;
    size_t not_ready_count;
    StreamUpdateResult last_update_result;
    StreamObserverOps const *stream_ops;
    StreamObserver *stream_observer;
};

template <typename Iter>
bool rewind_iterator_for_consensus_event(
    monad_exec_event_type consensus_event_type,
    std::optional<BlockLabel> const &opt_block_label, Iter *iter,
    StreamEvent *e)
{
    if (!opt_block_label) {
        return monad_exec_iter_consensus_prev(
            iter, consensus_event_type, &e->event, (void const **)&e->payload);
    }

    BlockLabel const &block_label = *opt_block_label;
    if (block_label.type == BlockLabel::Type::BlockNumber) {
        return consensus_event_type == MONAD_EXEC_NONE
                   ? monad_exec_iter_rewind_for_simple_replay(
                         iter,
                         block_label.block_number,
                         &e->event,
                         (void const **)&e->payload)
                   : monad_exec_iter_block_number_prev(
                         iter,
                         block_label.block_number,
                         consensus_event_type,
                         &e->event,
                         (void const **)&e->payload);
    }
    else {
        MONAD_ABORT(
            "extend the iter help interface to work with partial block IDs");
#if 0
        MONAD_ASSERT(block_label.type == BlockLabel::Type::BlockNumber);
        return monad_exec_iter_block_id_prev(
            iter,
            &block_label.block_id,
            consensus_event_type,
            &e->event,
            &e->payload);
#endif
    }
}

std::list<StreamObserverState>
create_stream_observer_states(std::span<StreamObserver *const> stream_observers)
{
    std::list<StreamObserverState> states;

    for (StreamObserver *so : stream_observers) {
        StreamObserverState &state = states.emplace_back();
        EventSourceSpec const &event_source = so->get_event_source();
        state.stream_ops = get_stream_observer_ops(so->command->type);
        state.stream_observer = so;
        if (std::string const err = state.stream_ops->init(so); !err.empty()) {
            errx_f(
                EX_SOFTWARE,
                "init of stream source{} failed: {}",
                event_source.describe(),
                err);
        }
    }

    for (StreamObserverState &s : states) {
        EventSourceSpec const &event_source =
            s.stream_observer->get_event_source();
        if (std::string const err =
                s.stream_observer->get_event_source().init_iterator(&s.iter);
            !err.empty()) {
            errx_f(
                EX_SOFTWARE,
                "init_iterator failed for stream source {}: {}",
                event_source.describe(),
                err);
        }
        if (event_source.source_query.consensus_event) {
            using enum EventIterator::Type;

            switch (s.iter.iter_type) {
            case EventRing:
                (void)rewind_iterator_for_consensus_event(
                    *event_source.source_query.consensus_event,
                    event_source.source_query.block,
                    &s.iter.ring.iter,
                    &s.stream_event);
                break;
            case EventCaptureSection:
                (void)rewind_iterator_for_consensus_event(
                    *event_source.source_query.consensus_event,
                    event_source.source_query.block,
                    &s.iter.evcap.iter,
                    &s.stream_event);
                break;
            case BlockArchive:
                MONAD_ABORT("block archives are not consensus-event seekable");
            default:
                std::unreachable();
            }
        }
        if (std::string const err =
                s.stream_ops->iter_init(s.stream_observer, &s.iter);
            !err.empty()) {
            errx_f(
                EX_SOFTWARE,
                "iter_init failed for stream source {}: {}",
                event_source.describe(),
                err);
        }
    }

    return states;
}

void update_stream_observers(std::list<StreamObserverState> &states)
{
    constexpr size_t NotReadyCheckMask = (1UL << 25) - 1;

    auto i_state = begin(states);
    auto const i_end_state = end(states);
    while (i_state != i_end_state) {
        using enum EventIteratorResult;

        auto const i_current = i_state++;
        StreamObserverState &state = *i_current;
        StreamObserver *const so = state.stream_observer;
        StreamEvent &e = state.stream_event;
        bool remove = false;

        ++e.poll_count;
        e.iter_result = state.iter.next(&e.event, &e.payload);

        switch (e.iter_result) {
        case Error:
            stream_warnx_f(
                so,
                "stream error: {} [{}]",
                state.iter.last_error_msg,
                state.iter.error_code);
            remove = true;
            break;

        case AfterEnd:
            // XXX: this potentially indicates an error condition that the
            // user might want to know about
            [[fallthrough]];
        case End:
            remove = true;
            break;

        case Skipped:
            break;

        case NotReady:
            if ((++state.not_ready_count & NotReadyCheckMask) == 0) {
                if (so->command->output != nullptr) {
                    fflush(so->command->output->file);
                }
                if (so->get_event_source().source_file->is_finalized()) {
                    remove = true;
                }
            }
            break;

        case Gap: {
            state.not_ready_count = 0;
            ++e.gap_count;
            state.last_update_result =
                state.stream_ops->update(so, &state.iter, &e);
            char const *const clear_action =
                state.last_update_result == StreamUpdateResult::Abort
                    ? "remove event source"
                    : "reset iterator";
            auto const [gap_seqno, new_seqno] = state.iter.clear_gap(!remove);
            stream_warnx_f(
                so,
                "event gap from {} -> {}, will {}",
                gap_seqno,
                new_seqno,
                clear_action);
        } break;

        case AfterBegin:
            [[fallthrough]];
        case Success:
            state.not_ready_count = 0;
            ++e.event_count;
            state.last_update_result =
                state.stream_ops->update(so, &state.iter, &e);
            break;
        }

        if (state.last_update_result == StreamUpdateResult::Abort || remove) {
            state.stream_ops->finish(so, state.last_update_result);
            states.erase(i_current);
        }
    }
}

} // end of anonymous namespace

void stream_thread_main(std::span<StreamObserver *const> stream_observers)
{
    std::list<StreamObserverState> states =
        create_stream_observer_states(stream_observers);

    while (g_should_exit == 0 && !states.empty()) {
        update_stream_observers(states);
    }

    for (StreamObserverState &s : states) {
        s.stream_ops->finish(s.stream_observer, s.last_update_result);
    }
}

std::string
rewind_to_block_boundary(StreamObserver const *so, EventIterator *iter)
{
    if (std::string s = expect_content_type(
            so->get_event_source(),
            MONAD_EVENT_CONTENT_TYPE_EXEC,
            iter->content_type);
        !s.empty()) {
        return s;
    }

    EventSourceSpec const &event_source = so->get_event_source();
    if (!event_source.source_query.consensus_event && !iter->begin_seqno &&
        event_source.source_file->get_type() ==
            EventSourceFile::Type::EventRing &&
        event_source.source_file->is_interactive()) {
        if (!monad_exec_iter_consensus_prev(
                &iter->ring.iter, MONAD_EXEC_NONE, nullptr, nullptr)) {
            return "rewind_to_block_boundary failed";
        }
    }
    return {};
}
