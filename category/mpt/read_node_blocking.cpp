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

#include <category/async/detail/scope_polyfill.hpp>
#include <category/core/assert.h>
#include <category/mpt/config.hpp>
#include <category/mpt/node.hpp>
#include <category/mpt/trie.hpp>
#include <category/mpt/util.hpp>

#include <errno.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include <cstdint>

MONAD_MPT_NAMESPACE_BEGIN

Node::UniquePtr read_node_blocking(
    UpdateAuxImpl const &aux, chunk_offset_t const node_offset,
    uint64_t const version)
{
    MONAD_ASSERT(aux.is_on_disk());
    if (!aux.version_is_valid_ondisk(version)) {
        return {};
    }
    auto &pool = aux.io->storage_pool();
    MONAD_DEBUG_ASSERT(
        node_offset.spare <=
        round_up_align<DISK_PAGE_BITS>(Node::max_disk_size));
    // spare bits are number of pages needed to load node
    unsigned const num_pages_to_load_node =
        node_disk_pages_spare_15{node_offset}.to_pages();
    unsigned const bytes_to_read = num_pages_to_load_node << DISK_PAGE_BITS;
    file_offset_t const rd_offset =
        round_down_align<DISK_PAGE_BITS>(node_offset.offset);
    uint16_t const buffer_off = uint16_t(node_offset.offset - rd_offset);
    auto *buffer =
        (unsigned char *)aligned_alloc(DISK_PAGE_SIZE, bytes_to_read);
    auto unbuffer = make_scope_exit([buffer]() noexcept { ::free(buffer); });

    auto chunk = pool.activate_chunk(pool.seq, node_offset.id);
    auto fd = chunk->read_fd();
    ssize_t const bytes_read = pread(
        fd.first,
        buffer,
        bytes_to_read,
        static_cast<off_t>(fd.second + rd_offset));
    if (bytes_read < 0) {
        MONAD_ABORT_PRINTF(
            "FATAL: pread(%u, %llu) failed with '%s'\n",
            bytes_to_read,
            rd_offset,
            strerror(errno));
    }
    return aux.version_is_valid_ondisk(version)
               ? deserialize_node_from_buffer<Node>(
                     buffer + buffer_off, size_t(bytes_read) - buffer_off)
               : Node::UniquePtr{};
}

MONAD_MPT_NAMESPACE_END
