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

#include <cstddef>
#include <cstdint>
#include <format>
#include <iterator>
#include <memory>
#include <string>

#include <fcntl.h>
#include <sys/mman.h>
#include <unistd.h>

#include <category/core/assert.h>
#include <category/core/cleanup.h>
#include <category/core/event/event_def.h>
#include <category/core/event/event_ring.h>
#include <category/core/mem/virtual_buf.h>
#include <category/execution/ethereum/event/blockcap.h>
#include <category/execution/ethereum/event/exec_event_ctypes.h>

#include <zstd.h>

namespace
{

struct State
{
    ~State() noexcept;

    monad_bcap_builder *block_builder;
    monad_bcap_finalize_tracker *finalize_tracker;
    monad_bcap_pack_writer *pack_writer;
    monad_bcap_archive *block_archive;
    monad_vbuf_mmap_allocator *vbuf_mmap_allocator;
    ZSTD_CCtx *event_zstd_cctx;
    ZSTD_CCtx *seqno_index_zstd_cctx;
};

State::~State() noexcept
{
    monad_bcap_builder_destroy(block_builder);
    monad_bcap_finalize_tracker_destroy(finalize_tracker);
    monad_bcap_archive_close(block_archive);
    monad_bcap_pack_writer_destroy(pack_writer);
    ZSTD_freeCCtx(event_zstd_cctx);
    ZSTD_freeCCtx(seqno_index_zstd_cctx);
}

constexpr mode_t CreateMode = S_IRUSR | S_IWUSR | S_IRGRP | S_IWGRP | S_IROTH;

std::string recordexec_init(StreamObserver *so)
{
    std::unique_ptr state = std::make_unique<State>();

    auto const *const options =
        so->command->get_options<RecordExecCommandOptions>();
    std::string const &output_spec = options->common_options.output_spec;

    int output_fd [[gnu::cleanup(cleanup_close)]];
    if (options->block_format == BlockRecordFormat::Archive) {
        // Output is underneath a top-level archive directory which must
        // already exist
        output_fd =
            open(output_spec.c_str(), O_RDONLY | O_DIRECTORY | O_CLOEXEC);
    }
    else {
        // Output is in a single file
        MONAD_ASSERT(options->block_format == BlockRecordFormat::Packed);
        output_fd =
            open(output_spec.c_str(), O_RDWR | O_CREAT | O_TRUNC, CreateMode);
    }
    if (output_fd == -1) {
        return std::format(
            "unable to open {} `{}`",
            options->block_format == BlockRecordFormat::Archive
                ? "block archive directory"
                : "evcap output file",
            output_spec.c_str());
    }

    EX_SET_OR_RETURN(
        state->event_zstd_cctx, create_zstd_cctx(options->event_zstd_level));
    EX_SET_OR_RETURN(
        state->seqno_index_zstd_cctx,
        create_zstd_cctx(options->seqno_zstd_level));

    VBUF_CHECK_INIT(monad_vbuf_mmap_allocator_create(
        &state->vbuf_mmap_allocator, options->vbuf_segment_shift, MAP_PRIVATE));
    BCAP_CHECK_INIT(monad_bcap_builder_create(
        &state->block_builder,
        (monad_vbuf_segment_allocator *)state->vbuf_mmap_allocator,
        (monad_vbuf_segment_allocator *)state->vbuf_mmap_allocator));
    BCAP_CHECK_INIT(
        monad_bcap_finalize_tracker_create(&state->finalize_tracker));
    if (options->block_format == BlockRecordFormat::Archive) {
        BCAP_CHECK_INIT(monad_bcap_archive_open(
            &state->block_archive, output_fd, output_spec.c_str()));
        state->pack_writer = nullptr;
    }
    else {
        BCAP_CHECK_INIT(monad_bcap_pack_writer_create(
            &state->pack_writer,
            output_fd,
            1U << options->pack_max_sections_shift));
        state->block_archive = nullptr;
    }

    so->state = state.release();
    return {};
}

std::string recordexec_iter_init(StreamObserver *so, EventIterator *iter)
{
    return rewind_to_block_boundary(so, iter);
}

StreamUpdateResult
recordexec_update(StreamObserver *so, EventIterator *iter, StreamEvent *e)
{
    if (e->iter_result != EventIteratorResult::Success) {
        return StreamUpdateResult::Abort;
    }

    monad_bcap_append_result append_result;
    monad_bcap_proposal *proposal;
    State *const state = so->get_state<State>();

    // Try to append the event to the block builder; we must always call
    // this function even for events we know aren't recorded, since the
    // block builder checks for sequence number gaps internally
    BCAP_CHECK_UPDATE(monad_bcap_builder_append_event(
        state->block_builder,
        &e->event,
        e->payload,
        &append_result,
        &proposal));

    if (e->event.event_type == MONAD_EXEC_BLOCK_FINALIZED) {
        monad_bcap_proposal_list abandon_chain;
        auto const block_tag =
            *reinterpret_cast<monad_exec_block_tag const *>(e->payload);
        if (!iter->check_payload(&e->event)) {
            stream_warnx_f(so, "payload expired for event {}", e->event.seqno);
            return StreamUpdateResult::Abort;
        }
        BCAP_CHECK_UPDATE(monad_bcap_finalize_tracker_update(
            state->finalize_tracker, &block_tag, &proposal, &abandon_chain));
        if (proposal == nullptr) {
            // Finalization for a block we never saw; this is near the
            // beginning of the sequence
            return StreamUpdateResult::Ok;
        }

        // TODO(ken): move writer infrastructure to a different thread,
        //  do compression and sync there
        if (state->block_archive != nullptr) {
            char path_buf[32];
            monad_evcap_writer *evcap_writer;
            monad_evcap_section_desc const *exec_schema_sd;

            // Open a writer to an anonymous capture file; this computes
            // the name the file will eventually have (into path_buf), but
            // won't link it into the filesystem yet, to prevent partial
            // writes from being seen
            BCAP_CHECK_UPDATE(monad_bcap_archive_open_block_writer(
                state->block_archive,
                proposal->block_tag.block_number,
                CreateMode | S_IXUSR | S_IXGRP | S_IXOTH,
                CreateMode,
                path_buf,
                sizeof path_buf,
                nullptr,
                &evcap_writer,
                &exec_schema_sd));

            // Write the block capture proposal into the file
            BCAP_CHECK_UPDATE(monad_bcap_write_proposal_evcap_ext(
                evcap_writer,
                proposal,
                exec_schema_sd,
                nullptr,
                nullptr,
                state->event_zstd_cctx,
                state->seqno_index_zstd_cctx));

            // Link the anonymous file into the filesystem at the name
            // computed earlier; also destroys the writer
            BCAP_CHECK_UPDATE(monad_bcap_archive_close_block_writer(
                state->block_archive,
                proposal->block_tag.block_number,
                evcap_writer,
                path_buf));
        }
        else {
            MONAD_ASSERT(state->pack_writer != nullptr);
            BCAP_CHECK_UPDATE(monad_bcap_pack_writer_add_block(
                state->pack_writer,
                proposal,
                state->event_zstd_cctx,
                state->seqno_index_zstd_cctx));
        }
        monad_bcap_proposal_free(proposal);

        while ((proposal = TAILQ_FIRST(&abandon_chain)) != nullptr) {
            TAILQ_REMOVE(&abandon_chain, proposal, entry);
            monad_bcap_proposal_free(proposal);
        }
        return StreamUpdateResult::Ok;
    }

    if (append_result == MONAD_BCAP_OUTSIDE_BLOCK_SCOPE) {
        return StreamUpdateResult::Ok;
    }

    if (!iter->check_payload(&e->event)) {
        stream_warnx_f(so, "payload expired for event {}", e->event.seqno);
        return StreamUpdateResult::Abort;
    }

    if (append_result == MONAD_BCAP_PROPOSAL_ABORTED) {
        if (e->event.event_type == MONAD_EXEC_BLOCK_REJECT) {
            monad_bcap_proposal_free(proposal);
            return StreamUpdateResult::Ok;
        }
        MONAD_ASSERT_PRINTF(
            e->event.event_type == MONAD_EXEC_EVM_ERROR,
            "proposal aborted on unexpected event type %s [%hu]",
            g_monad_exec_event_metadata[e->event.event_type].c_name,
            e->event.event_type);
        auto const *const error_info =
            reinterpret_cast<monad_exec_evm_error const *>(e->payload);
        stream_warnx_f(
            so,
            "cannot record after EVM error {}:{}",
            error_info->domain_id,
            error_info->status_code);
        return StreamUpdateResult::Abort;
    }

    if (append_result == MONAD_BCAP_PROPOSAL_FINISHED) {
        MONAD_DEBUG_ASSERT(proposal != nullptr);
        monad_bcap_finalize_tracker_add_proposal(
            state->finalize_tracker, proposal);
    }

    return StreamUpdateResult::Ok;
}

void recordexec_finish(StreamObserver *so, StreamUpdateResult)
{
    delete so->get_state<State>();
}

} // End of anonymous namespace

StreamObserverOps const recordexec_ops = {
    .init = recordexec_init,
    .iter_init = recordexec_iter_init,
    .update = recordexec_update,
    .finish = recordexec_finish,
};
