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

#include <errno.h>
#include <stdbit.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

#include <sys/mman.h>
#include <sys/types.h>

#include <category/core/event/evcap_file.h>
#include <category/core/event/evcap_writer.h>
#include <category/core/event/event_def.h>
#include <category/core/format_err.h>
#include <category/core/srcloc.h>
#include <category/execution/ethereum/event/blockcap.h>
#include <category/execution/ethereum/event/exec_event_ctypes.h>

// Defined in blockcap_builder.c
extern thread_local char _g_monad_bcap_error_buf[1024];

#define FORMAT_ERRC(...)                                                       \
    monad_format_err(                                                          \
        _g_monad_bcap_error_buf,                                               \
        sizeof(_g_monad_bcap_error_buf),                                       \
        &MONAD_SOURCE_LOCATION_CURRENT(),                                      \
        __VA_ARGS__)

// XXX: fixed size index of 256k blocks for now
constexpr uint32_t PACK_INDEX_CAPACITY = 1U << 18;

struct monad_bcap_pack_writer
{
    struct monad_evcap_writer *evcap_writer;
    struct monad_bcap_pack_index_entry *index_entries;
    struct monad_evcap_section_desc const *schema_sd;
    size_t index_entries_map_len;
    struct monad_evcap_pack_index_desc *index_desc;
    bool desynchronized;
};

#if !defined(__clang__)

static inline void write_index_entry(
    struct monad_bcap_pack_index_entry *address,
    struct monad_bcap_pack_index_entry *value)
{

    __asm__ __volatile__("vmovdqa %1, %0" : "=m"(*address) : "x"(*value));
}

#else

static inline void write_index_entry(
    struct monad_bcap_pack_index_entry *address,
    struct monad_bcap_pack_index_entry *value)
{
    __atomic_store(address, value, __ATOMIC_RELEASE);
}

#endif

int monad_bcap_pack_writer_create(
    struct monad_bcap_pack_writer **pkw_p, int fd, unsigned max_sections)
{
    int rc;
    struct monad_bcap_pack_writer *pkw;
    struct monad_evcap_section_desc *index_sd;
    struct monad_evcap_writer_create_options const evcap_writer_opts = {
        .sectab_entries_shift =
            (uint8_t)stdc_trailing_zeros(stdc_bit_ceil(max_sections)),
        .append = false};

    *pkw_p = pkw = malloc(sizeof *pkw);
    if (pkw == nullptr) {
        return FORMAT_ERRC(errno, "malloc of monad_bcap_pack_writer failed");
    }
    memset(pkw, 0, sizeof *pkw);
    rc = monad_evcap_writer_create(&pkw->evcap_writer, fd, &evcap_writer_opts);
    if (rc != 0) {
        goto EVCAP_Error;
    }
    rc = monad_evcap_writer_add_schema_section(
        pkw->evcap_writer,
        MONAD_EVENT_CONTENT_TYPE_EXEC,
        g_monad_exec_event_schema_hash,
        &pkw->schema_sd);
    if (rc != 0) {
        goto EVCAP_Error;
    }

    // Allocate an empty pack index section in the file, and mark it active
    pkw->index_entries_map_len =
        PACK_INDEX_CAPACITY * sizeof(struct monad_bcap_pack_index_entry);
    rc = monad_evcap_writer_alloc_empty_section(
        pkw->evcap_writer, &pkw->index_entries_map_len, &index_sd);
    index_sd->type = MONAD_EVCAP_SECTION_PACK_INDEX;
    if (rc != 0) {
        goto EVCAP_Error;
    }
    pkw->index_entries = mmap(
        nullptr,
        pkw->index_entries_map_len,
        PROT_READ | PROT_WRITE,
        MAP_SHARED,
        monad_evcap_writer_get_fd(pkw->evcap_writer),
        (off_t)index_sd->content_offset);
    if (pkw->index_entries == MAP_FAILED) {
        rc =
            FORMAT_ERRC(errno, "mmap of bcap_pack_writer index entries failed");
        goto Error;
    }
    pkw->index_desc = &index_sd->pack_index;
    pkw->index_desc->entry_capacity = PACK_INDEX_CAPACITY;
    __atomic_store_n(&pkw->index_desc->is_active, true, __ATOMIC_RELEASE);

    return 0;

EVCAP_Error:
    FORMAT_ERRC(
        rc,
        "cannot create bcap pack writer, caused by:\n%s",
        monad_evcap_writer_get_last_error());
Error:
    monad_bcap_pack_writer_destroy(pkw);
    *pkw_p = nullptr;
    return rc;
}

void monad_bcap_pack_writer_destroy(struct monad_bcap_pack_writer *pkw)
{
    if (pkw != nullptr) {
        __atomic_store_n(&pkw->index_desc->is_active, false, __ATOMIC_RELEASE);
        if (pkw->index_entries != nullptr) {
            (void)munmap(pkw->index_entries, pkw->index_entries_map_len);
        }
        monad_evcap_writer_destroy(pkw->evcap_writer);
        free(pkw);
    }
}

struct monad_evcap_writer *
monad_bcap_pack_writer_get_evcap_writer(struct monad_bcap_pack_writer *pkw)
{
    return pkw->evcap_writer;
}

int monad_bcap_pack_writer_add_block(
    struct monad_bcap_pack_writer *pkw,
    struct monad_bcap_proposal const *proposal, ZSTD_CCtx *event_zstd_cctx,
    ZSTD_CCtx *seqno_index_zstd_cctx)
{
    struct monad_evcap_section_desc *event_sd;
    int rc;

    if (pkw->desynchronized) {
        return FORMAT_ERRC(ENOTRECOVERABLE, "blockcap writer desynchronized");
    }
    if (pkw->index_desc->block_count == pkw->index_desc->entry_capacity) {
        return FORMAT_ERRC(
            ENOSPC,
            "block index is full, all %u entries used",
            pkw->index_desc->block_count);
    }
    rc = monad_bcap_write_proposal_evcap_ext(
        pkw->evcap_writer,
        proposal,
        pkw->schema_sd,
        &event_sd,
        nullptr,
        event_zstd_cctx,
        seqno_index_zstd_cctx);
    if (rc != 0) {
        pkw->desynchronized = true;
        return rc;
    }

    write_index_entry(
        &pkw->index_entries[pkw->index_desc->block_count],
        &(struct monad_bcap_pack_index_entry){
            .block_number = proposal->block_tag.block_number,
            .section_desc_offset = event_sd->content_offset,
        });

    if (pkw->index_desc->block_count == 0) {
        __atomic_store_n(
            &pkw->index_desc->start_block,
            proposal->block_tag.block_number,
            __ATOMIC_RELEASE);
    }
    __atomic_fetch_add(&pkw->index_desc->block_count, 1, __ATOMIC_ACQ_REL);
    return 0;
}
