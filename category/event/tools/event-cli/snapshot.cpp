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
#include "options.hpp"
#include "stream.hpp"
#include "util.hpp"

#include <algorithm>
#include <bit>
#include <cstddef>
#include <cstdint>
#include <cstdlib>
#include <cstring>
#include <filesystem>
#include <memory>
#include <print>
#include <span>
#include <stdexcept>
#include <string>
#include <utility>

#include <signal.h>
#include <stdio.h>
#include <sys/mman.h>
#include <sys/queue.h>
#include <sys/types.h>
#include <sysexits.h>
#include <unistd.h>

#include <category/core/assert.h>
#include <category/core/event/evcap_file.h>
#include <category/core/event/evcap_reader.h>
#include <category/core/event/event_def.h>
#include <category/core/event/event_ring.h>
#include <category/core/event/event_ring_util.h>
#include <category/core/mem/align.h>
#include <category/core/mem/virtual_buf.h>
#include <category/execution/ethereum/event/exec_event_ctypes.h>

namespace fs = std::filesystem;

namespace
{

constexpr size_t PAGE_2MB = 1UL << 21;

inline void VBUF_CHECK_THROW(int rc)
{
    if (rc != 0) [[unlikely]] {
        throw std::runtime_error{std::format(
            "vbuf library error -- {}", monad_vbuf_writer_get_last_error())};
    }
}

struct snapshot_vbuf_state
{
    struct monad_vbuf_writer *writer;
    struct monad_vbuf_chain chain;
};

class SnapshotWriter
{
public:
    explicit SnapshotWriter(
        EventSourceFile const *source_file, uint8_t segment_shift)
        : source_file_{source_file}
        , event_count_{0}
        , last_block_ref_{0}
    {
        VBUF_CHECK_THROW(monad_vbuf_mmap_allocator_create(
            &vbuf_segment_alloc_, segment_shift, MAP_PRIVATE));
        VBUF_CHECK_THROW(monad_vbuf_writer_create(
            &descriptor_vbuf_state_.writer,
            (monad_vbuf_segment_allocator *)vbuf_segment_alloc_));
        VBUF_CHECK_THROW(monad_vbuf_writer_create(
            &payload_vbuf_state_.writer,
            (monad_vbuf_segment_allocator *)vbuf_segment_alloc_));
        monad_vbuf_chain_init(&descriptor_vbuf_state_.chain);
        monad_vbuf_chain_init(&payload_vbuf_state_.chain);

        EventSourceFile::Type const file_type = source_file_->get_type();
        if (file_type == EventSourceFile::Type::EventRing) {
            header_ = *static_cast<MappedEventRing const *>(source_file_)
                           ->get_header();
        }
        else {
            MONAD_ASSERT_PRINTF(
                file_type == EventSourceFile::Type::EventCaptureFile,
                "do not know how init header from source type %hhu",
                std::to_underlying(file_type));
            EventCaptureFile const *const capture =
                static_cast<EventCaptureFile const *>(source_file_);
            monad_evcap_reader const *const evcap_reader =
                capture->get_reader();
            monad_evcap_section_desc const *sd = nullptr;

            uint8_t const *schema_hash = nullptr;
            while (monad_evcap_reader_next_section(
                evcap_reader, MONAD_EVCAP_SECTION_SCHEMA, &sd)) {
                if (schema_hash != nullptr) {
                    errx_f(
                        EX_CONFIG,
                        "capture file {} contains multiple metadata sections",
                        source_file_->describe());
                }
                memcpy(
                    header_.magic, sd->schema.ring_magic, sizeof header_.magic);
                header_.content_type = sd->schema.content_type;
                schema_hash = sd->schema.schema_hash;
            }
            if (schema_hash == nullptr) {
                errx_f(
                    EX_CONFIG,
                    "capture file {} had no schema section",
                    source_file_->describe());
            }
            memcpy(
                header_.schema_hash, schema_hash, sizeof header_.schema_hash);
            header_.size.context_area_size = 0;
        }
    }

    ~SnapshotWriter()
    {
        for (auto *vs : {&descriptor_vbuf_state_, &payload_vbuf_state_}) {
            monad_vbuf_chain flushed;
            monad_vbuf_writer_destroy(vs->writer, &flushed);
            monad_vbuf_chain_free(
                monad_vbuf_chain_concat(&vs->chain, &flushed));
        }
        monad_vbuf_mmap_allocator_destroy(vbuf_segment_alloc_);
    }

    StreamUpdateResult append_event(
        StreamObserver *so, EventIterator const *iter,
        monad_event_descriptor const *event, std::byte const *payload,
        bool erase_timestamps)
    {
        uint64_t const buf_offset = get_payload_buf_virtual_offset();
        VBUF_CHECK_UPDATE(monad_vbuf_writer_memcpy(
            payload_vbuf_state_.writer,
            payload,
            event->payload_size,
            MONAD_EVENT_PAYLOAD_ALIGN,
            &payload_vbuf_state_.chain));
        if (!iter->check_payload(event)) {
            errx_f(
                EX_SOFTWARE,
                "ERROR: event {} payload lost! OFFSET: {}, WINDOW_START: "
                "{}",
                event->seqno,
                event->payload_buf_offset,
                iter->ring.mapped_event_ring->get_buffer_window_start());
        }

        monad_event_descriptor event_copy = *event;
        event_copy.seqno = ++event_count_;
        event_copy.payload_buf_offset = buf_offset;
        if (erase_timestamps) {
            event_copy.record_epoch_nanos = 0;
        }

        // TODO(ken): we don't like having special logic for different
        //   ring types, but it's not clear how else to handle this; figure
        //   something out...
        if (header_.content_type == MONAD_EVENT_CONTENT_TYPE_EXEC &&
            event_copy.content_ext[MONAD_FLOW_BLOCK_SEQNO] != 0) {
            if (event_copy.event_type == MONAD_EXEC_BLOCK_START) {
                last_block_ref_ = event_copy.seqno;
            }
            event_copy.content_ext[MONAD_FLOW_BLOCK_SEQNO] = last_block_ref_;
        }

        VBUF_CHECK_UPDATE(monad_vbuf_writer_memcpy(
            descriptor_vbuf_state_.writer,
            &event_copy,
            sizeof event_copy,
            alignof(monad_event_descriptor),
            &descriptor_vbuf_state_.chain));

        return StreamUpdateResult::Ok;
    }

    // TODO(ken): some errx_f calls not removed yet
    void write_snapshot(int fd, fs::path const &output_path)
    {
        // Flush the residual vbuf segments onto their respective chains
        for (auto *vs : {&descriptor_vbuf_state_, &payload_vbuf_state_}) {
            monad_vbuf_chain flushed;
            monad_vbuf_chain_init(&flushed);
            monad_vbuf_writer_flush(vs->writer, &flushed);
            monad_vbuf_chain_concat(&vs->chain, &flushed);
        }

        uint64_t const next_payload_byte = get_payload_buf_virtual_offset();
        header_.size.descriptor_capacity = std::max<uint64_t>(
            std::bit_ceil(event_count_),
            1UL << MONAD_EVENT_MIN_DESCRIPTORS_SHIFT);
        header_.size.payload_buf_size = std::max<uint64_t>(
            std::bit_ceil(next_payload_byte),
            1UL << MONAD_EVENT_MIN_PAYLOAD_BUF_SHIFT);

        header_.control.last_seqno = event_count_;
        header_.control.next_payload_byte = next_payload_byte;
        header_.control.buffer_window_start = 0;

        std::print(
            stderr,
            "writing {} events to {}, total size is: {}",
            header_.size.descriptor_capacity,
            output_path.string(),
            monad_event_ring_calc_storage(&header_.size));

        checked_write(fd, &header_, sizeof header_);
        skip_bytes(fd, PAGE_2MB - sizeof header_);

        monad_vbuf_segment *segment;
        size_t count = 0;
        TAILQ_FOREACH(segment, &descriptor_vbuf_state_.chain.segments, entry)
        {
            copy_vbuf_segment(fd, segment);
            std::print(
                stderr,
                " ... D:{}/{}",
                ++count,
                descriptor_vbuf_state_.chain.segment_count);
        }

        uint64_t const descriptor_skip =
            header_.size.descriptor_capacity * sizeof(monad_event_descriptor) -
            monad_vbuf_writer_get_offset(descriptor_vbuf_state_.writer);
        skip_bytes(fd, descriptor_skip);

        count = 0;
        TAILQ_FOREACH(segment, &payload_vbuf_state_.chain.segments, entry)
        {
            copy_vbuf_segment(fd, segment);
            std::print(
                stderr,
                " ... P:{}/{}",
                ++count,
                payload_vbuf_state_.chain.segment_count);
        }

        uint64_t const payload_skip =
            header_.size.payload_buf_size - next_payload_byte;
        skip_bytes(fd, payload_skip);

        if (source_file_->get_type() == EventSourceFile::Type::EventRing) {
            auto const *const mr =
                static_cast<MappedEventRing const *>(source_file_);
            checked_write(
                fd,
                mr->get_event_ring()->context_area,
                header_.size.context_area_size);
        }
        std::println(stderr, " ... done");
    }

private:
    uint64_t get_payload_buf_virtual_offset()
    {
        return monad_round_size_to_align(
            monad_vbuf_writer_get_offset(payload_vbuf_state_.writer),
            MONAD_EVENT_PAYLOAD_ALIGN);
    }

    void skip_bytes(int out_fd, size_t n_bytes)
    {
        // Usually the output is a pipe (stdout piped into the stdin of the
        // zstd compression CLI utility), so we can't skip bytes with lseek
        // or splice `/dev/zero` into `fd`; we need to actually write zeros
        while (n_bytes > PAGE_2MB) {
            checked_write(out_fd, Zero.get(), PAGE_2MB);
            n_bytes -= PAGE_2MB;
        }
        checked_write(out_fd, Zero.get(), n_bytes);
    }

    void copy_vbuf_segment(int out_fd, monad_vbuf_segment *vs)
    {
        size_t residual = vs->written;
        uint8_t *next = vs->map_base;
        while (residual > 0) {
            ssize_t const n_written = write(out_fd, next, residual);
            if (n_written == -1) {
                err_f(EX_OSERR, "sendfile failed");
            }
            next += static_cast<size_t>(n_written);
            residual -= static_cast<size_t>(n_written);
        }
    }

    void checked_write(int fd, void const *buf, size_t n)
    {
        auto const *p = static_cast<std::byte const *>(buf);
        auto const *const end = p + n;
        while (p != end) {
            ssize_t const n_written =
                write(fd, p, static_cast<size_t>(end - p));
            if (n_written == -1) {
                err_f(EX_OSERR, "write of {} bytes failed", n);
            }
            p += static_cast<size_t>(n_written);
        }
    }

    EventSourceFile const *source_file_;

    monad_vbuf_mmap_allocator *vbuf_segment_alloc_;
    snapshot_vbuf_state descriptor_vbuf_state_;
    snapshot_vbuf_state payload_vbuf_state_;
    uint64_t event_count_;
    uint64_t last_block_ref_;
    monad_event_ring_header header_;

    static std::unique_ptr<std::byte[]> Zero;
};

std::unique_ptr<std::byte[]> SnapshotWriter::Zero{new std::byte[PAGE_2MB]{}};

struct State
{
    SnapshotWriter snap_writer;
    SnapshotCommandOptions const *options;
};

void kill_event_ring_writers(int ring_fd, int sig)
{
    monad_event_flock_info flocks[32];
    size_t lock_count = std::size(flocks);
    if (monad_event_ring_query_flocks(ring_fd, flocks, &lock_count) == -1) {
        errx_f(
            EX_SOFTWARE,
            "library error: {}",
            monad_event_ring_get_last_error());
    }
    for (size_t i = 0; i < lock_count; ++i) {
        kill(flocks[i].pid, sig);
    }
}

std::string snapshot_init(StreamObserver *so)
{
    auto const *const options =
        so->command->get_options<SnapshotCommandOptions>();
    try {
        State *const state = new State{SnapshotWriter{
            so->get_event_source().source_file, options->vbuf_segment_shift}};
        state->options = options;
        so->state = state;
        return {};
    }
    catch (std::runtime_error const &ex) {
        return ex.what();
    }
}

std::string snapshot_iter_init(StreamObserver *, EventIterator *)
{
    return {};
}

StreamUpdateResult
snapshot_update(StreamObserver *so, EventIterator *iter, StreamEvent *e)
{
    if (e->iter_result != EventIteratorResult::Success) {
        return StreamUpdateResult::Abort;
    }
    State *const state = so->get_state<State>();
    return state->snap_writer.append_event(
        so, iter, &e->event, e->payload, state->options->erase_timestamps);
}

void snapshot_finish(StreamObserver *so, StreamUpdateResult r)
{
    State *const state = so->get_state<State>();

    if (r == StreamUpdateResult::Ok) {
        EventSourceFile const *const file = so->get_event_source().source_file;
        if (state->options->kill_at_end &&
            file->get_type() == EventSourceFile::Type::EventRing) {
            kill_event_ring_writers(file->get_file_descriptor(), SIGINT);
        }

        OutputFile const *o = so->command->output;
        state->snap_writer.write_snapshot(fileno(o->file), o->canonical_path);
    }

    delete state;
}

} // End of anonymous namespace

StreamObserverOps const snapshot_ops = {
    .init = snapshot_init,
    .iter_init = snapshot_iter_init,
    .update = snapshot_update,
    .finish = snapshot_finish};
