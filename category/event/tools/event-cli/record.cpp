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

#include "err_cxx.hpp"
#include "file.hpp"
#include "iterator.hpp"
#include "metadata.hpp"
#include "options.hpp"
#include "stream.hpp"
#include "util.hpp"

#include <cstddef>
#include <format>
#include <memory>
#include <optional>
#include <string>

#include <errno.h>
#include <fcntl.h>
#include <string.h>
#include <sys/mman.h>
#include <sys/queue.h>
#include <sys/types.h>
#include <unistd.h>

#include <category/core/assert.h>
#include <category/core/cleanup.h>
#include <category/core/event/evcap_file.h>
#include <category/core/event/evcap_writer.h>
#include <category/core/event/event_ring.h>
#include <category/core/mem/align.h>
#include <category/core/mem/virtual_buf.h>

#include <zstd.h>

extern char const *__progname;

namespace
{

[[nodiscard]] std::string safe_write(int fd, void *buf, size_t length)
{
    ssize_t n_written;
    do {
        n_written = write(fd, buf, length);
        if (n_written == -1) {
            return std::format(
                "unable write {} bytes to fd={}: {} [{}]",
                length,
                fd,
                strerror(errno),
                errno);
        }
        buf = static_cast<std::byte *>(buf) + static_cast<size_t>(n_written);
        length -= static_cast<size_t>(n_written);
    }
    while (length > 0);
    return {};
}

struct event_vbuf
{
    monad_vbuf_chain vbuf_chain;
    monad_vbuf_writer *vbuf_writer;
    monad_evcap_dynamic_section *dynsec;
    monad_evcap_section_desc *event_bundle_sd;
    std::unique_ptr<std::byte[]> zstd_buf;
    size_t zstd_buf_size;
    ZSTD_CCtx *zstd_cctx;
};

struct seqno_index_vbuf
{
    monad_vbuf_chain vbuf_chain;
    monad_vbuf_writer *vbuf_writer;
    int memfd;
    std::unique_ptr<std::byte[]> zstd_buf;
    size_t zstd_buf_size;
    size_t content_length;
    size_t file_length;
    ZSTD_CCtx *zstd_cctx;
};

[[nodiscard]] std::string init_event_vbuf(
    monad_evcap_writer *evcap_writer, monad_evcap_section_desc const *schema_sd,
    monad_vbuf_mmap_allocator *mmap_allocator,
    RecordCommandOptions const *options, event_vbuf *evb)
{
    monad_vbuf_chain_init(&evb->vbuf_chain);
    VBUF_CHECK_INIT(monad_vbuf_writer_create(
        &evb->vbuf_writer, (monad_vbuf_segment_allocator *)mmap_allocator));
    if (monad_evcap_writer_dynsec_open(
            evcap_writer, &evb->dynsec, &evb->event_bundle_sd) != 0) {
        return std::format(
            "evcap library error -- {}", monad_evcap_writer_get_last_error());
    }
    evb->event_bundle_sd->type = MONAD_EVCAP_SECTION_EVENT_BUNDLE;
    evb->event_bundle_sd->event_bundle.schema_desc_offset =
        schema_sd->descriptor_offset;
    EX_SET_OR_RETURN(
        evb->zstd_cctx, create_zstd_cctx(options->event_zstd_level));
    if (evb->zstd_cctx) {
        evb->event_bundle_sd->compression =
            MONAD_EVCAP_COMPRESSION_ZSTD_STREAMING;
        evb->zstd_buf_size = ZSTD_CStreamOutSize();
        evb->zstd_buf = std::make_unique<std::byte[]>(evb->zstd_buf_size);
    }
    else {
        evb->event_bundle_sd->compression = MONAD_EVCAP_COMPRESSION_NONE;
        evb->zstd_buf_size = 0;
    }
    return {};
}

bool drain_event_vbuf(
    StreamObserver *so, monad_evcap_writer *evcap_writer, event_vbuf *evb,
    ZSTD_EndDirective end_directive)
{
    monad_vbuf_segment *vs;

    while ((vs = TAILQ_FIRST(&evb->vbuf_chain.segments)) != nullptr) {
        monad_vbuf_chain_remove(&evb->vbuf_chain, vs);
        if (evb->zstd_cctx == nullptr) {
            // No compression
            if (monad_evcap_writer_dynsec_write(
                    evcap_writer, evb->dynsec, vs->map_base, vs->written) < 0) {
                stream_warnx_f(
                    so,
                    "evcap library error -- {}",
                    monad_evcap_writer_get_last_error());
                return false;
            }
        }
        else {
            ZSTD_inBuffer in_buf = {
                .src = vs->map_base, .size = vs->written, .pos = 0};
            bool finished;
            do {
                ZSTD_outBuffer out_buf = {
                    .dst = evb->zstd_buf.get(),
                    .size = evb->zstd_buf_size,
                    .pos = 0};
                size_t const zbuf_remaining = ZSTD_compressStream2(
                    evb->zstd_cctx, &out_buf, &in_buf, end_directive);
                if (ZSTD_isError(zbuf_remaining)) {
                    stream_warnx_f(
                        so,
                        "ZSTD_compressStream2 failed in vbuf: {}",
                        ZSTD_getErrorName(zbuf_remaining));
                    return false;
                }
                if (monad_evcap_writer_dynsec_write(
                        evcap_writer, evb->dynsec, out_buf.dst, out_buf.pos) <
                    0) {
                    stream_warnx_f(
                        so,
                        "evcap library error -- {}",
                        monad_evcap_writer_get_last_error());
                    return false;
                }
                finished = end_directive == ZSTD_e_end
                               ? zbuf_remaining == 0
                               : in_buf.pos == in_buf.size;
            }
            while (!finished);
        }
        evb->event_bundle_sd->content_length += vs->written;
        monad_vbuf_segment_free(vs);
    }
    return true;
}

[[nodiscard]] std::string init_seqno_index_vbuf(
    monad_vbuf_mmap_allocator *mmap_allocator,
    RecordCommandOptions const *options, seqno_index_vbuf *svb)
{
    monad_vbuf_chain_init(&svb->vbuf_chain);
    VBUF_CHECK_INIT(monad_vbuf_writer_create(
        &svb->vbuf_writer, (monad_vbuf_segment_allocator *)mmap_allocator));
    svb->memfd = memfd_create("seqno-index", 0);
    if (svb->memfd == -1) {
        return std::format(
            "unable to memfd_create(2) seqno index: {} [{}]",
            strerror(errno),
            errno);
    }
    EX_SET_OR_RETURN(
        svb->zstd_cctx, create_zstd_cctx(options->seqno_zstd_level));
    if (svb->zstd_cctx) {
        svb->zstd_buf_size = ZSTD_CStreamOutSize();
        svb->zstd_buf = std::make_unique<std::byte[]>(svb->zstd_buf_size);
    }
    else {
        svb->zstd_buf_size = 0;
    }
    return {};
}

bool drain_seqno_index_vbuf(
    StreamObserver *so, seqno_index_vbuf *svb, ZSTD_EndDirective end_directive)
{
    monad_vbuf_segment *vs;

    while ((vs = TAILQ_FIRST(&svb->vbuf_chain.segments)) != nullptr) {
        monad_vbuf_chain_remove(&svb->vbuf_chain, vs);
        if (svb->zstd_cctx == nullptr) {
            // No compression
            if (std::string const err =
                    safe_write(svb->memfd, vs->map_base, vs->written);
                !err.empty()) {
                stream_warnx_f(so, "safe_write failed: {}", err);
                return false;
            }
            svb->file_length += vs->written;
        }
        else {
            ZSTD_inBuffer in_buf = {
                .src = vs->map_base, .size = vs->written, .pos = 0};
            bool finished;
            do {
                ZSTD_outBuffer out_buf = {
                    .dst = svb->zstd_buf.get(),
                    .size = svb->zstd_buf_size,
                    .pos = 0};
                size_t const zbuf_remaining = ZSTD_compressStream2(
                    svb->zstd_cctx, &out_buf, &in_buf, end_directive);
                if (ZSTD_isError(zbuf_remaining)) {
                    stream_warnx_f(
                        so,
                        "ZSTD_compressStream2 failed in vbuf: {}",
                        ZSTD_getErrorName(zbuf_remaining));
                    return false;
                }
                if (std::string const err =
                        safe_write(svb->memfd, out_buf.dst, out_buf.pos);
                    !err.empty()) {
                    stream_warnx_f(so, "safe_write failed: {}", err);
                    return false;
                }
                svb->file_length += out_buf.pos;
                finished = end_directive == ZSTD_e_end
                               ? zbuf_remaining == 0
                               : in_buf.pos == in_buf.size;
            }
            while (!finished);
        }
        svb->content_length += vs->written;
        monad_vbuf_segment_free(vs);
    }

    return true;
}

struct State
{
    ~State() noexcept;

    monad_vbuf_mmap_allocator *vbuf_mmap_allocator;
    monad_evcap_writer *evcap_writer;
    event_vbuf event_vb;
    std::optional<seqno_index_vbuf> opt_seqno_index_vb;
};

State::~State() noexcept
{
    if (event_vb.vbuf_writer != nullptr) {
        monad_vbuf_writer_destroy(event_vb.vbuf_writer, &event_vb.vbuf_chain);
        MONAD_ASSERT(event_vb.vbuf_chain.segment_count == 0);
        monad_vbuf_chain_free(&event_vb.vbuf_chain);
        ZSTD_freeCCtx(event_vb.zstd_cctx);
    }
    if (opt_seqno_index_vb) {
        seqno_index_vbuf &svb = *opt_seqno_index_vb;
        monad_vbuf_writer_destroy(svb.vbuf_writer, &svb.vbuf_chain);
        MONAD_ASSERT(svb.vbuf_chain.segment_count == 0);
        monad_vbuf_chain_free(&svb.vbuf_chain);
        ZSTD_freeCCtx(svb.zstd_cctx);
    }
    monad_evcap_writer_destroy(evcap_writer);
    monad_vbuf_mmap_allocator_destroy(vbuf_mmap_allocator);
}

std::string record_init(StreamObserver *so)
{
    constexpr mode_t CreateMode =
        S_IRUSR | S_IWUSR | S_IRGRP | S_IWGRP | S_IROTH;

    std::unique_ptr state = std::make_unique<State>();
    auto const *const options =
        so->command->get_options<RecordCommandOptions>();
    std::string const &output_spec = options->common_options.output_spec;
    int fd [[gnu::cleanup(cleanup_close)]] =
        open(output_spec.c_str(), O_RDWR | O_CREAT | O_TRUNC, CreateMode);
    if (fd == -1) {
        return std::format(
            "unable to open fd to record output file `{}`: {} [{}]",
            output_spec.c_str(),
            strerror(errno),
            errno);
    }
    monad_evcap_writer_create_options const evcap_writer_options = {
        .sectab_entries_shift = 0, .append = false};
    EVCAP_CHECK_INIT(monad_evcap_writer_create(
        &state->evcap_writer, fd, &evcap_writer_options));

    VBUF_CHECK_INIT(monad_vbuf_mmap_allocator_create(
        &state->vbuf_mmap_allocator, options->vbuf_segment_shift, MAP_PRIVATE));

    so->state = state.release();
    return {};
}

std::string record_iter_init(StreamObserver *so, EventIterator *iter)
{
    State *const state = so->get_state<State>();
    auto const *const options =
        so->command->get_options<RecordCommandOptions>();

    monad_evcap_section_desc const *schema_sd;
    EVCAP_CHECK_INIT(monad_evcap_writer_add_schema_section(
        state->evcap_writer,
        iter->content_type,
        *MetadataTable[iter->content_type].schema_hash,
        &schema_sd));

    // vbuf initialization
    if (std::string err = init_event_vbuf(
            state->evcap_writer,
            schema_sd,
            state->vbuf_mmap_allocator,
            options,
            &state->event_vb);
        !err.empty()) {
        return err;
    }
    if (!options->no_seqno_index) {
        if (std::string err = init_seqno_index_vbuf(
                state->vbuf_mmap_allocator,
                options,
                &state->opt_seqno_index_vb.emplace());
            !err.empty()) {
            return err;
        }
    }

    return {};
}

StreamUpdateResult
record_update(StreamObserver *so, EventIterator *iter, StreamEvent *e)
{
    State *const state = so->get_state<State>();

    if (e->iter_result != EventIteratorResult::Success) {
        return StreamUpdateResult::Abort;
    }

    if (state->opt_seqno_index_vb) {
        seqno_index_vbuf &svb = *state->opt_seqno_index_vb;
        size_t const cur_event_offset = monad_round_size_to_align(
            monad_vbuf_writer_get_offset(state->event_vb.vbuf_writer),
            alignof(monad_event_descriptor));
        VBUF_CHECK_UPDATE(monad_vbuf_writer_memcpy(
            svb.vbuf_writer,
            &cur_event_offset,
            sizeof cur_event_offset,
            1,
            &svb.vbuf_chain));
        if (svb.vbuf_chain.segment_count > 0 &&
            !drain_seqno_index_vbuf(so, &svb, ZSTD_e_continue)) {
            return StreamUpdateResult::Abort;
        }
    }
    VBUF_CHECK_UPDATE(monad_evcap_vbuf_append_event(
        state->event_vb.vbuf_writer,
        &e->event,
        e->payload,
        &state->event_vb.vbuf_chain));
    if (!iter->check_payload(&e->event)) {
        stream_warnx_f(so, "payload expired for event {}", e->event.seqno);
        return StreamUpdateResult::Abort;
    }
    if (state->event_vb.event_bundle_sd->event_bundle.event_count++ == 0) {
        state->event_vb.event_bundle_sd->event_bundle.start_seqno =
            e->event.seqno;
    }
    if (state->event_vb.vbuf_chain.segment_count > 0 &&
        !drain_event_vbuf(
            so, state->evcap_writer, &state->event_vb, ZSTD_e_continue)) {
        return StreamUpdateResult::Abort;
    }

    return StreamUpdateResult::Ok;
}

void record_finish(StreamObserver *so, StreamUpdateResult r)
{
    State *const state = so->get_state<State>();

    monad_vbuf_writer_flush(
        state->event_vb.vbuf_writer, &state->event_vb.vbuf_chain);
    if (!drain_event_vbuf(
            so, state->evcap_writer, &state->event_vb, ZSTD_e_end)) {
        r = StreamUpdateResult::Abort;
    }
    (void)monad_evcap_writer_dynsec_close(
        state->evcap_writer, state->event_vb.dynsec);

    if (state->opt_seqno_index_vb) {
        seqno_index_vbuf &svb = *state->opt_seqno_index_vb;
        monad_vbuf_writer_flush(svb.vbuf_writer, &svb.vbuf_chain);
        if (!drain_seqno_index_vbuf(so, &svb, ZSTD_e_end)) {
            r = StreamUpdateResult::Abort;
        }

        monad_evcap_section_desc *seqno_index_sd = nullptr;
        void *const map_base = mmap(
            nullptr, svb.file_length, PROT_READ, MAP_PRIVATE, svb.memfd, 0);
        if (map_base == MAP_FAILED) {
            stream_warn_f(so, "unable to mmap seqno index memfd for write");
            r = StreamUpdateResult::Abort;
        }
        else {
            if (monad_evcap_writer_new_section(
                    state->evcap_writer,
                    map_base,
                    svb.file_length,
                    &seqno_index_sd) < 0) {
                stream_warnx_f(
                    so,
                    "evcap library error -- {}",
                    monad_evcap_writer_get_last_error());
                r = StreamUpdateResult::Abort;
            }
            munmap(map_base, svb.file_length);
        }

        if (seqno_index_sd != nullptr) {
            seqno_index_sd->type = MONAD_EVCAP_SECTION_SEQNO_INDEX;
            seqno_index_sd->compression =
                svb.zstd_cctx ? MONAD_EVCAP_COMPRESSION_ZSTD_STREAMING
                              : MONAD_EVCAP_COMPRESSION_NONE;
            seqno_index_sd->content_length = svb.content_length;
            seqno_index_sd->seqno_index.event_bundle_desc_offset =
                state->event_vb.event_bundle_sd->descriptor_offset;

            state->event_vb.event_bundle_sd->event_bundle
                .seqno_index_desc_offset = seqno_index_sd->descriptor_offset;
        }
    }

    // TODO(ken): unlink the file if r == StreamUpdateResult::Abort
    (void)r;

    delete state;
}

} // end of anonymous namespace

StreamObserverOps const record_ops = {
    .init = record_init,
    .iter_init = record_iter_init,
    .update = record_update,
    .finish = record_finish,
};
