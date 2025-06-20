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
#include "err_cxx.hpp"
#include "file.hpp"
#include "iterator.hpp"
#include "metadata.hpp"
#include "options.hpp"
#include "stream.hpp"

#include <chrono>
#include <cstddef>
#include <cstdint>
#include <cstdio>
#include <format>
#include <iterator>
#include <memory>
#include <print>
#include <span>
#include <string>
#include <utility>

#include <category/core/event/event_def.h>
#include <category/core/event/event_metadata.h>
#include <category/execution/ethereum/event/exec_event_ctypes.h>
#include <category/execution/ethereum/event/exec_event_ctypes_fmt.hpp>
#include <category/execution/ethereum/event/exec_iter_help.h>

#if !USE_CHRONO_TIME_ZONE
    #include <time.h>
#endif

namespace
{

bool hexdump_event_payload(
    EventIterator const *iter, monad_event_descriptor const *event,
    std::byte const *const payload_base, std::FILE *out)
{
    // Large thread_locals will cause a stack overflow, so make the
    // thread-local a pointer to a dynamic buffer
    constexpr size_t hexdump_buf_size = 1UL << 25;
    thread_local static std::unique_ptr<char[]> const hexdump_buf{
        new char[hexdump_buf_size]};

    bool const overflow = event->payload_size > hexdump_buf_size;
    std::byte const *const payload_end =
        overflow ? reinterpret_cast<std::byte *>(hexdump_buf.get()) +
                       hexdump_buf_size
                 : payload_base + event->payload_size;
    char *o = hexdump_buf.get();
    for (std::byte const *line = payload_base; line < payload_end; line += 16) {
        // Print one line of the dump, which is 16 bytes, in the form:
        // <offset> <8 bytes> <8 bytes>
        o = std::format_to(o, "{:#08x} ", line - payload_base);
        for (uint8_t b = 0; b < 16 && line + b < payload_end; ++b) {
            o = std::format_to(o, "{:02x}", std::to_underlying(line[b]));
            if (b == 7) {
                *o++ = ' '; // Extra padding after 8 bytes
            }
        }
        *o++ = '\n';

        // Every 512 bytes, check if the payload data is still valid; the +16
        // bias is to prevent checking the first iteration
        if ((line - payload_base + 16) % 512 == 0 &&
            !iter->check_payload(event)) {
            break; // Escape to the end, which checks the final time
        }
    }

    if (!iter->check_payload(event)) {
        return false;
    }
    std::fwrite(
        hexdump_buf.get(), static_cast<size_t>(o - hexdump_buf.get()), 1, out);
    if (overflow) {
        std::println(
            out,
            "ERROR: hexdump overflowed; event payload size {}, hexdump buffer "
            "size {}",
            event->payload_size,
            hexdump_buf_size);
    }
    return true;
}

char *format_exec_event_content_ext_array(
    EventIterator const *iter, monad_event_descriptor const *event,
    std::byte const *payload, char *o)
{
    if (event->content_ext[MONAD_FLOW_BLOCK_SEQNO] != 0) {
        uint64_t block_number;
        if (monad_exec_get_block_number(
                iter->get_evsrc_any(), event, payload, &block_number)) {
            o = std::format_to(o, " BLK: {}", block_number);
        }
        else {
            o = std::format_to(o, " BLK: <LOST>");
        }
    }
    if (uint64_t const txn_id = event->content_ext[MONAD_FLOW_TXN_ID]) {
        o = std::format_to(o, " TXN: {}", txn_id - 1);
    }
    return o;
}

bool print_event(
    EventIterator const *iter, monad_event_descriptor const *event,
    std::byte const *payload, DumpCommandOptions const *dump_opts,
    std::FILE *out)
{
    using std::chrono::seconds, std::chrono::nanoseconds;
    static std::chrono::sys_time<seconds> last_second{};
    static std::chrono::sys_time<nanoseconds> last_second_nanos;
    static char time_buf[32];
    char unknown_name_buf[16];
    char event_buf[512];

    monad_event_metadata const *const event_md =
        iter->content_type < std::size(MetadataTable)
            ? &MetadataTable[iter->content_type].event_meta[event->event_type]
            : nullptr;
    if (event_md == nullptr) {
        *std::format_to(unknown_name_buf, "???[{}]", event->event_type) = '\0';
    }

    std::chrono::sys_time const event_time{
        nanoseconds{event->record_epoch_nanos}};

    // An optimization to only do the string formatting of the %H:%M:%S part
    // of the time each second when it changes; this is a slow operation
    if (auto const cur_second = std::chrono::floor<seconds>(event_time);
        cur_second != last_second) {
#if USE_CHRONO_TIME_ZONE
        std::chrono::zoned_time const event_time_tz{
            std::chrono::current_zone(), cur_second};
        *std::format_to(time_buf, "{:%T}", event_time_tz) = '\0';
#else
        time_t const cs =
            static_cast<time_t>(cur_second.time_since_epoch().count());
        strftime(time_buf, sizeof time_buf, "%H:%M:%S", localtime(&cs));
#endif
        last_second = cur_second;
        last_second_nanos =
            std::chrono::time_point_cast<nanoseconds>(last_second);
    }

    // Print a summary line of this event
    // <HH:MM::SS.nanos> <event-c-name> [<event-type> <event-type-hex>]
    //     SEQ: <sequence-no> LEN: <payload-length>
    char *o = std::format_to(
        event_buf,
        "{}.{:09}: {} [{} {:#x}] SEQ: {} LEN: {} BUF_OFF: {}",
        time_buf,
        (event_time - last_second_nanos).count(),
        event_md ? event_md->c_name : unknown_name_buf,
        event->event_type,
        event->event_type,
        event->seqno,
        event->payload_size,
        event->payload_buf_offset);

    // Print the `event->content_ext` array. There are two different approaches:
    //
    //   1. For execution rings the program understands the meaning of these
    //      values and prints them in an ergonomic way, e.g.,
    //      `event->content_ext[MONAD_FLOW_TXN_ID]` is a transaction index
    //      number so it prints that as `TXN: <number>`
    //
    //   2. For all other rings, or if explicitly requested for debugging
    //      purposes, the hex value of each array element is printed
    if (dump_opts->always_dump_content_ext ||
        iter->content_type != MONAD_EVENT_CONTENT_TYPE_EXEC) {
        o = std::format_to(o, " CONTENT_EXT:");
        for (uint64_t const u : event->content_ext) {
            o = std::format_to(o, " {0:#08x}", u);
        }
    }
    switch (iter->content_type) {
    case MONAD_EVENT_CONTENT_TYPE_EXEC:
        o = format_exec_event_content_ext_array(iter, event, payload, o);
        break;
    default:
        break;
    }
    *o++ = '\n';
    std::fwrite(event_buf, static_cast<size_t>(o - event_buf), 1, out);
    bool payload_ok = true;

    if (dump_opts->decode && event->payload_size > 0) {
        // TODO(ken): generalize a decode interface beyond the exec ring
        std::string buf;
        std::back_insert_iterator mbo{buf};

        switch (iter->content_type) {
        case MONAD_EVENT_CONTENT_TYPE_EXEC:
            mbo = category_labs::format_as(
                mbo,
                payload,
                static_cast<monad_exec_event_type>(event->event_type));
            break;
        default:
            break;
        }
        if (!buf.empty()) {
            if (iter->check_payload(event)) {
                std::println(out, "{}", buf);
            }
            else {
                payload_ok = false;
            }
        }
    }
    if (dump_opts->hexdump) {
        payload_ok = hexdump_event_payload(iter, event, payload, out);
    }
    return payload_ok;
}

std::string dump_init(StreamObserver *)
{
    return {};
}

std::string dump_iter_init(StreamObserver *, EventIterator *)
{
    return {};
}

StreamUpdateResult
dump_update(StreamObserver *so, EventIterator *iter, StreamEvent *e)
{
    if (e->iter_result == EventIteratorResult::Gap) {
        return StreamUpdateResult::Ok;
    }

    auto const *const options = so->command->get_options<DumpCommandOptions>();
    std::FILE *const out = so->command->output->file;
    bool const payload_ok =
        print_event(iter, &e->event, e->payload, options, out);
    if (!payload_ok) {
        stream_warnx_f(
            so,
            "event {} payload lost! OFFSET: {}, WINDOW_START: {}",
            e->event.seqno,
            e->event.payload_buf_offset,
            iter->ring.mapped_event_ring->get_buffer_window_start());
        (void)iter->clear_gap(true);
    }

    return StreamUpdateResult::Ok;
}

void dump_finish(StreamObserver *, StreamUpdateResult) {}

} // End of anonymous namespace

StreamObserverOps const dump_ops = {
    .init = dump_init,
    .iter_init = dump_iter_init,
    .update = dump_update,
    .finish = dump_finish};
