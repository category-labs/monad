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

#include <category/core/event/evcap_file.h>
#include <category/core/event/evcap_writer.h>
#include <category/core/format_err.h>
#include <category/core/srcloc.h>
#include <category/execution/ethereum/event/blockcap.h>

#include <zstd.h>

// Defined in blockcap_builder.c
extern thread_local char _g_monad_bcap_error_buf[1024];

#define FORMAT_ERRC(...)                                                       \
    monad_format_err(                                                          \
        _g_monad_bcap_error_buf,                                               \
        sizeof(_g_monad_bcap_error_buf),                                       \
        &MONAD_SOURCE_LOCATION_CURRENT(),                                      \
        __VA_ARGS__)

int monad_bcap_write_proposal_evcap_ext(
    struct monad_evcap_writer *ecw, struct monad_bcap_proposal const *proposal,
    struct monad_evcap_section_desc const *schema_sd,
    struct monad_evcap_section_desc **event_sd_p,
    struct monad_evcap_section_desc **seqno_index_sd_p,
    ZSTD_CCtx *event_zstd_cctx, ZSTD_CCtx *seqno_index_zstd_cctx)
{
    int rc;
    struct monad_evcap_dynamic_section *dynsec;
    struct monad_evcap_section_desc *event_sd;
    struct monad_evcap_section_desc *seqno_index_sd;

    if (event_sd_p != nullptr) {
        *event_sd_p = nullptr;
    }
    if (seqno_index_sd_p != nullptr) {
        *seqno_index_sd_p = nullptr;
    }

    // Flush the proposal's event vbuf chain to a dynamic section
    rc = monad_evcap_writer_dynsec_open(ecw, &dynsec, &event_sd);
    if (rc != 0) {
        goto EVCAP_Error;
    }
    event_sd->type = MONAD_EVCAP_SECTION_EVENT_BUNDLE;
    event_sd->compression = event_zstd_cctx != nullptr
                                ? MONAD_EVCAP_COMPRESSION_ZSTD_SINGLE_PASS
                                : MONAD_EVCAP_COMPRESSION_NONE;
    event_sd->content_length = proposal->event_vbuf_chain.vbuf_length;
    event_sd->event_bundle.schema_desc_offset = schema_sd->descriptor_offset;
    event_sd->event_bundle.event_count = proposal->event_count;
    event_sd->event_bundle.start_seqno = proposal->start_seqno;
    event_sd->event_bundle.block_number = proposal->block_tag.block_number;

    rc = (int)monad_evcap_writer_dynsec_sync_vbuf_chain(
        ecw, dynsec, &proposal->event_vbuf_chain, event_zstd_cctx);
    if (rc < 0) {
        rc = -rc;
        goto EVCAP_Error;
    }
    rc = monad_evcap_writer_dynsec_close(ecw, dynsec);
    if (rc != 0) {
        goto EVCAP_Error;
    }

    // If we have a seqno vbuf chain, flush that too
    if (proposal->seqno_index_vbuf_chain.segment_count > 0) {
        rc = monad_evcap_writer_dynsec_open(ecw, &dynsec, &seqno_index_sd);
        if (rc != 0) {
            goto EVCAP_Error;
        }
        seqno_index_sd->type = MONAD_EVCAP_SECTION_SEQNO_INDEX;
        seqno_index_sd->compression =
            seqno_index_zstd_cctx != nullptr
                ? MONAD_EVCAP_COMPRESSION_ZSTD_SINGLE_PASS
                : MONAD_EVCAP_COMPRESSION_NONE;
        seqno_index_sd->content_length =
            proposal->seqno_index_vbuf_chain.vbuf_length;
        seqno_index_sd->seqno_index.event_bundle_desc_offset =
            event_sd->descriptor_offset;

        event_sd->event_bundle.seqno_index_desc_offset =
            seqno_index_sd->descriptor_offset;

        rc = (int)monad_evcap_writer_dynsec_sync_vbuf_chain(
            ecw,
            dynsec,
            &proposal->seqno_index_vbuf_chain,
            seqno_index_zstd_cctx);
        if (rc < 0) {
            rc = -rc;
            goto EVCAP_Error;
        }
        rc = monad_evcap_writer_dynsec_close(ecw, dynsec);
        if (rc != 0) {
            goto EVCAP_Error;
        }
    }
    if (event_sd_p != nullptr) {
        *event_sd_p = event_sd;
    }
    if (seqno_index_sd_p != nullptr) {
        *seqno_index_sd_p = seqno_index_sd;
    }
    return 0;

EVCAP_Error:
    return FORMAT_ERRC(
        rc,
        "cannot write finalized block %lu, caused by:\n%s",
        (unsigned long)proposal->block_tag.block_number,
        monad_evcap_writer_get_last_error());
}
