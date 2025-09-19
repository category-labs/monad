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

#include <category/core/assert.h>

#include <category/async/config.hpp>
#include <category/core/test_util/gtest_signal_stacktrace_printer.hpp> // NOLINT
#include <category/mpt/config.hpp>
#include <category/mpt/node.hpp>
#include <category/mpt/trie.hpp>

#include <cstddef>
#include <cstdint>

using namespace MONAD_MPT_NAMESPACE;
using namespace MONAD_ASYNC_NAMESPACE;

namespace
{
    Node::UniquePtr make_node_of_size(unsigned const node_disk_size)
    {
        MONAD_ASSERT(node_disk_size > sizeof(Node) + Node::disk_size_bytes);
        auto const node_value_size =
            node_disk_size - sizeof(Node) - Node::disk_size_bytes;
        auto const value = monad::byte_string(node_value_size, 0xf);
        auto node = make_node(0, {}, {}, value, {}, 0);
        return node;
    }
}

template <
    size_t storage_pool_chunk_size = 1 << 28,
    size_t storage_pool_num_chunks = 64, bool use_anonoymous_inode = true>
struct NodeWriterTestBase : public ::testing::Test
{
    static constexpr size_t chunk_size = storage_pool_chunk_size;
    static constexpr size_t num_chunks = storage_pool_num_chunks;

    storage_pool pool;
    monad::io::Ring ring1;
    monad::io::Ring ring2;
    monad::io::Buffers rwbuf;
    AsyncIO io;
    UpdateAux<> aux;

    NodeWriterTestBase()
        : pool{[] {
            storage_pool::creation_flags flags;
            auto const bitpos = std::countr_zero(storage_pool_chunk_size);
            flags.chunk_capacity = bitpos;
            if constexpr (use_anonoymous_inode) {
                return storage_pool(use_anonymous_inode_tag{}, flags);
            }
            char temppath[] = "monad_test_fixture_XXXXXX";
            int const fd = mkstemp(temppath);
            if (-1 == fd) {
                abort();
            }
            if (-1 == ftruncate(fd, (3 + num_chunks) * chunk_size + 24576)) {
                abort();
            }
            ::close(fd);
            std::filesystem::path temppath2(temppath);
            return MONAD_ASYNC_NAMESPACE::storage_pool(
                {&temppath2, 1},
                MONAD_ASYNC_NAMESPACE::storage_pool::mode::create_if_needed,
                flags);
        }()}
        , ring1{2}
        , ring2{4}
        , rwbuf{monad::io::make_buffers_for_segregated_read_write(
              ring1, ring2, 2, 4, AsyncIO::MONAD_IO_BUFFERS_READ_SIZE,
              AsyncIO::MONAD_IO_BUFFERS_WRITE_SIZE)}
        , io{pool, rwbuf}
        , aux{&io}
    {
    }

    ~NodeWriterTestBase()
    {
        for (auto &device : pool.devices()) {
            auto const path = device.current_path();
            if (std::filesystem::exists(path)) {
                std::filesystem::remove(path);
            }
        }
    }

    void node_writer_append_dummy_bytes(
        node_writer_unique_ptr_type &node_writer, size_t bytes)
    {
        while (bytes > 0) {
            auto &sender = node_writer->sender();
            auto const remaining_bytes = sender.remaining_buffer_bytes();
            if (bytes <= remaining_bytes) {
                sender.advance_buffer_append(bytes);
                return;
            }
            if (remaining_bytes > 0) {
                sender.advance_buffer_append(remaining_bytes);
                bytes -= remaining_bytes;
            }

            auto new_node_writer = replace_node_writer(aux, node_writer);
            MONAD_ASSERT(new_node_writer);
            node_writer->initiate();
            // shall be recycled by the i/o receiver
            node_writer.release();
            node_writer = std::move(new_node_writer);
        }
    }

    uint32_t get_writer_chunk_id(node_writer_unique_ptr_type &node_writer)
    {
        return node_writer->sender().offset().id;
    }

    uint32_t get_writer_chunk_count(node_writer_unique_ptr_type &node_writer)
    {
        return (uint32_t)aux.db_metadata()
            ->at(get_writer_chunk_id(node_writer))
            ->insertion_count();
    }
};

using NodeWriterTest = NodeWriterTestBase<>;

TEST_F(NodeWriterTest, write_nodes_each_within_buffer)
{
    auto const node_writer_chunk_id_before =
        get_writer_chunk_id(aux.node_writer_fast);
    auto const node_writer_chunk_count_before =
        get_writer_chunk_count(aux.node_writer_fast);
    ASSERT_EQ(node_writer_chunk_count_before, 0);

    unsigned const node_disk_size = 1024;
    unsigned const num_nodes =
        AsyncIO::MONAD_IO_BUFFERS_WRITE_SIZE / node_disk_size;
    auto node = make_node_of_size(node_disk_size);
    for (unsigned i = 0; i < num_nodes; ++i) {
        auto const node_offset = async_write_node_set_spare(aux, *node, true);
        EXPECT_EQ(node_offset.offset, node_disk_size * i);

        EXPECT_EQ(node_offset.id, get_writer_chunk_id(aux.node_writer_fast));
        EXPECT_EQ(
            get_writer_chunk_id(aux.node_writer_fast),
            node_writer_chunk_id_before);
        EXPECT_EQ(
            aux.node_writer_fast->sender().written_buffer_bytes(),
            node_offset.offset + node_disk_size);
    }
    // first buffer is full
    EXPECT_EQ(aux.node_writer_fast->sender().remaining_buffer_bytes(), 0);
    // continue write more node, node writer will switch to next buffer
    auto const node_offset = async_write_node_set_spare(aux, *node, true);
    EXPECT_EQ(node_offset.offset, AsyncIO::MONAD_IO_BUFFERS_WRITE_SIZE);
    EXPECT_EQ(
        get_writer_chunk_id(aux.node_writer_fast), node_writer_chunk_id_before);
    EXPECT_EQ(node_offset.id, node_writer_chunk_id_before);
    EXPECT_EQ(
        aux.node_writer_fast->sender().written_buffer_bytes(), node_disk_size);
}

TEST_F(NodeWriterTest, write_node_across_buffers_ends_at_buffer_boundary)
{
    // prepare less than 3 chunks
    auto const chunk_remaining_bytes =
        2 * AsyncIO::MONAD_IO_BUFFERS_WRITE_SIZE + 1024;
    MONAD_ASSERT(chunk_remaining_bytes < chunk_size);
    node_writer_append_dummy_bytes(
        aux.node_writer_fast, 3 * chunk_size - chunk_remaining_bytes);

    auto const node_writer_chunk_count_before =
        get_writer_chunk_count(aux.node_writer_fast);
    EXPECT_EQ(node_writer_chunk_count_before, 2);

    // node spans buffer 3 buffers
    auto node = make_node_of_size(chunk_remaining_bytes);
    auto const node_offset = async_write_node_set_spare(aux, *node, true);
    EXPECT_EQ(
        get_writer_chunk_count(aux.node_writer_fast),
        node_writer_chunk_count_before);
    EXPECT_EQ(node_offset.id, get_writer_chunk_id(aux.node_writer_fast));
    EXPECT_EQ(aux.node_writer_fast->sender().remaining_buffer_bytes(), 0);

    // write another node, node writer will switch to next buffer at next chunk
    auto const new_node_offset = async_write_node_set_spare(aux, *node, true);
    EXPECT_EQ(new_node_offset.offset, 0);
    auto const node_writer_chunk_count_after =
        get_writer_chunk_count(aux.node_writer_fast);
    EXPECT_EQ(
        aux.db_metadata()->at(new_node_offset.id)->insertion_count(),
        node_writer_chunk_count_after);
    EXPECT_EQ(
        node_writer_chunk_count_before + 1, node_writer_chunk_count_after);
    EXPECT_EQ(
        aux.node_writer_fast->sender().written_buffer_bytes(),
        chunk_remaining_bytes % AsyncIO::MONAD_IO_BUFFERS_WRITE_SIZE);
}

TEST_F(NodeWriterTest, write_node_at_new_chunk)
{
    // prepare less than 3 chunks
    auto const chunk_remaining_bytes = 1024;
    node_writer_append_dummy_bytes(
        aux.node_writer_fast, 3 * chunk_size - chunk_remaining_bytes);

    auto const node_writer_chunk_count_before_write_node =
        get_writer_chunk_count(aux.node_writer_fast);
    EXPECT_EQ(node_writer_chunk_count_before_write_node, 2);

    // make a node that is too big to fit in current chunk
    auto node = make_node_of_size(chunk_remaining_bytes + 1024);
    auto const node_offset = async_write_node_set_spare(aux, *node, true);
    auto const node_offset_chunk_count =
        aux.db_metadata()->at(node_offset.id)->insertion_count();
    EXPECT_EQ(
        node_offset_chunk_count, node_writer_chunk_count_before_write_node + 1);
    EXPECT_EQ(
        node_offset_chunk_count, get_writer_chunk_count(aux.node_writer_fast));
}
