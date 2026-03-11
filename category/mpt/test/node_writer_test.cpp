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
    Node::SharedPtr make_node_of_size(unsigned const node_disk_size)
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
    UpdateAux aux;

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
        , ring1{monad::io::RingConfig{2}}
        , ring2{monad::io::RingConfig{4}}
        , rwbuf{monad::io::make_buffers_for_segregated_read_write(
              ring1, ring2, 2, 4, AsyncIO::MONAD_IO_BUFFERS_READ_SIZE,
              AsyncIO::MONAD_IO_BUFFERS_WRITE_SIZE)}
        , io{pool, rwbuf}
        , aux{io}
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
                bytes = 0;
                break;
            }
            if (remaining_bytes > 0) {
                sender.advance_buffer_append(remaining_bytes);
                bytes -= remaining_bytes;
            }

            // Determine if this is fast or slow writer from chunk metadata
            bool is_fast = aux.db_metadata()
                               ->at(node_writer->sender().offset().id)
                               ->in_fast_list;

            // Compute aligned target offset for new buffer
            auto current_offset = node_writer->sender().offset();
            auto written = node_writer->sender().written_buffer_bytes();
            file_offset_t next_pos = current_offset.offset + written;
            next_pos = round_up_align<DISK_PAGE_BITS>(next_pos);

            auto chunk_capacity = aux.io->chunk_capacity(current_offset.id);
            chunk_offset_t target_offset{0, 0};

            // Check if we need next chunk
            if (next_pos >= chunk_capacity) {
                // Need next chunk - allocate it (test helper behavior)
                auto const *ci_ = aux.db_metadata()->free_list_end();
                MONAD_ASSERT(ci_ != nullptr);
                auto idx = ci_->index(aux.db_metadata());

                aux.remove(idx);
                aux.append(
                    is_fast ? UpdateAuxImpl::chunk_list::fast
                            : UpdateAuxImpl::chunk_list::slow,
                    idx);

                target_offset = chunk_offset_t{idx, 0};
            }
            else {
                target_offset = chunk_offset_t{
                    static_cast<uint32_t>(current_offset.id),
                    static_cast<uint32_t>(next_pos) &
                        chunk_offset_t::max_offset};
            }

            // Initiate old buffer I/O, then allocate new one. If all write
            // buffers are in flight, poll until one completes and frees up.
            node_writer->receiver().reset(
                node_writer->sender().written_buffer_bytes());
            node_writer->initiate();
            node_writer.release();
            node_writer_unique_ptr_type new_node_writer;
            while (
                !(new_node_writer =
                      replace_node_writer(aux, target_offset, is_fast))) {
                aux.io->poll_blocking(1);
            }
            node_writer = std::move(new_node_writer);
        }

        // Update write_position to match the physical node_writer position
        bool is_fast = aux.db_metadata()
                           ->at(node_writer->sender().offset().id)
                           ->in_fast_list;
        auto &write_pos = aux.writer(is_fast).write_position;
        auto const &sender = node_writer->sender();
        write_pos.current_chunk_id = sender.offset().id;
        write_pos.current_offset =
            sender.offset().offset + sender.written_buffer_bytes();
    }

    // Block until all delayed writes for the given writer are drained.
    // With non-blocking buffer allocation, process_delayed_writes may
    // return with items still queued. This helper polls io_uring until
    // completions re-trigger draining and the queue is empty.
    void drain_delayed_writes(bool is_fast)
    {
        auto &ws = aux.writer(is_fast);
        while (!ws.delayed_writes.empty()) {
            aux.io->poll_blocking(1);
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
        get_writer_chunk_id(aux.writer_fast.node_writer);
    auto const node_writer_chunk_count_before =
        get_writer_chunk_count(aux.writer_fast.node_writer);
    ASSERT_EQ(node_writer_chunk_count_before, 0);

    unsigned const node_disk_size = 1024;
    unsigned const num_nodes =
        AsyncIO::MONAD_IO_BUFFERS_WRITE_SIZE / node_disk_size;
    auto node = make_node_of_size(node_disk_size);
    for (unsigned i = 0; i < num_nodes; ++i) {
        auto const node_offset = async_write_node_set_spare(aux, node, true);
        EXPECT_EQ(node_offset.offset, node_disk_size * i);

        EXPECT_EQ(
            node_offset.id, get_writer_chunk_id(aux.writer_fast.node_writer));
        EXPECT_EQ(
            get_writer_chunk_id(aux.writer_fast.node_writer),
            node_writer_chunk_id_before);
        EXPECT_EQ(
            aux.writer_fast.node_writer->sender().written_buffer_bytes(),
            node_offset.offset + node_disk_size);
    }
    // first buffer is full
    EXPECT_EQ(
        aux.writer_fast.node_writer->sender().remaining_buffer_bytes(), 0);
    // continue write more node, node writer will switch to next buffer
    auto const node_offset = async_write_node_set_spare(aux, node, true);
    drain_delayed_writes(true);
    EXPECT_EQ(node_offset.offset, AsyncIO::MONAD_IO_BUFFERS_WRITE_SIZE);
    EXPECT_EQ(
        get_writer_chunk_id(aux.writer_fast.node_writer),
        node_writer_chunk_id_before);
    EXPECT_EQ(node_offset.id, node_writer_chunk_id_before);
    EXPECT_EQ(
        aux.writer_fast.node_writer->sender().written_buffer_bytes(),
        node_disk_size);
}

TEST_F(NodeWriterTest, write_node_across_buffers_ends_at_buffer_boundary)
{
    // prepare less than 3 chunks
    auto const chunk_remaining_bytes =
        2 * AsyncIO::MONAD_IO_BUFFERS_WRITE_SIZE + 1024;
    MONAD_ASSERT(chunk_remaining_bytes < chunk_size);
    node_writer_append_dummy_bytes(
        aux.writer_fast.node_writer, 3 * chunk_size - chunk_remaining_bytes);

    auto const node_writer_chunk_count_before =
        get_writer_chunk_count(aux.writer_fast.node_writer);
    EXPECT_EQ(node_writer_chunk_count_before, 2);

    // node spans buffer 3 buffers
    auto node = make_node_of_size(chunk_remaining_bytes);
    auto const node_offset = async_write_node_set_spare(aux, node, true);
    drain_delayed_writes(true);
    EXPECT_EQ(
        get_writer_chunk_count(aux.writer_fast.node_writer),
        node_writer_chunk_count_before);
    EXPECT_EQ(node_offset.id, get_writer_chunk_id(aux.writer_fast.node_writer));
    EXPECT_EQ(
        aux.writer_fast.node_writer->sender().remaining_buffer_bytes(), 0);

    // write another node, node writer will switch to next buffer at next chunk
    auto const new_node_offset = async_write_node_set_spare(aux, node, true);
    drain_delayed_writes(true);
    EXPECT_EQ(new_node_offset.offset, 0);
    auto const node_writer_chunk_count_after =
        get_writer_chunk_count(aux.writer_fast.node_writer);
    EXPECT_EQ(
        aux.db_metadata()->at(new_node_offset.id)->insertion_count(),
        node_writer_chunk_count_after);
    EXPECT_EQ(
        node_writer_chunk_count_before + 1, node_writer_chunk_count_after);
    EXPECT_EQ(
        aux.writer_fast.node_writer->sender().written_buffer_bytes(),
        chunk_remaining_bytes % AsyncIO::MONAD_IO_BUFFERS_WRITE_SIZE);
}

TEST_F(NodeWriterTest, write_node_at_new_chunk)
{
    // prepare less than 3 chunks
    auto const chunk_remaining_bytes = 1024;
    node_writer_append_dummy_bytes(
        aux.writer_fast.node_writer, 3 * chunk_size - chunk_remaining_bytes);

    auto const node_writer_chunk_count_before_write_node =
        get_writer_chunk_count(aux.writer_fast.node_writer);
    EXPECT_EQ(node_writer_chunk_count_before_write_node, 2);

    // make a node that is too big to fit in current chunk
    auto node = make_node_of_size(chunk_remaining_bytes + 1024);
    auto const node_offset = async_write_node_set_spare(aux, node, true);
    drain_delayed_writes(true);
    auto const node_offset_chunk_count =
        aux.db_metadata()->at(node_offset.id)->insertion_count();
    EXPECT_EQ(
        node_offset_chunk_count, node_writer_chunk_count_before_write_node + 1);
    EXPECT_EQ(
        node_offset_chunk_count,
        get_writer_chunk_count(aux.writer_fast.node_writer));
}

// Tests for the delayed write queue
TEST_F(NodeWriterTest, delayed_write_node_larger_than_remaining_buffer)
{
    // Fill the buffer so only a small amount remains
    unsigned const node_disk_size = 1024;
    auto small_node = make_node_of_size(node_disk_size);
    unsigned const num_nodes =
        AsyncIO::MONAD_IO_BUFFERS_WRITE_SIZE / node_disk_size;

    // Fill buffer to exactly full minus one node
    for (unsigned i = 0; i < num_nodes - 1; ++i) {
        async_write_node_set_spare(aux, small_node, true);
    }
    auto const remaining =
        aux.writer_fast.node_writer->sender().remaining_buffer_bytes();
    ASSERT_EQ(remaining, node_disk_size);

    // Write a node larger than remaining buffer - triggers delayed write path
    unsigned const large_node_size = node_disk_size * 2;
    auto large_node = make_node_of_size(large_node_size);
    auto const offset = async_write_node_set_spare(aux, large_node, true);

    // Offset should be allocated correctly
    EXPECT_NE(offset.offset, 0u);

    // write_position should have advanced past the large node
    EXPECT_GE(
        aux.writer_fast.write_position.current_offset,
        offset.offset + large_node_size);

    // I/O should complete and delayed writes should drain
    aux.io->flush();
    EXPECT_TRUE(aux.writer_fast.delayed_writes.empty());
}

TEST_F(NodeWriterTest, multiple_delayed_writes_maintain_order)
{
    unsigned const node_disk_size = 1024;
    auto small_node = make_node_of_size(node_disk_size);
    unsigned const num_nodes =
        AsyncIO::MONAD_IO_BUFFERS_WRITE_SIZE / node_disk_size;

    // Fill buffer completely
    for (unsigned i = 0; i < num_nodes; ++i) {
        async_write_node_set_spare(aux, small_node, true);
    }
    ASSERT_EQ(
        aux.writer_fast.node_writer->sender().remaining_buffer_bytes(), 0);

    // Write multiple nodes that must be queued - they can't fit in the
    // full buffer. The first write triggers the delayed path, subsequent
    // writes append to the non-empty queue.
    unsigned const large_node_size = node_disk_size * 2;
    auto large_node = make_node_of_size(large_node_size);
    auto const offset0 = async_write_node_set_spare(aux, large_node, true);
    auto const offset1 = async_write_node_set_spare(aux, large_node, true);
    auto const offset2 = async_write_node_set_spare(aux, large_node, true);

    // Offsets must be monotonically increasing (ordered allocation)
    EXPECT_GT(offset1.raw(), offset0.raw());
    EXPECT_GT(offset2.raw(), offset1.raw());

    // Flush all I/O - delayed writes should be fully drained
    aux.io->flush();
    EXPECT_TRUE(aux.writer_fast.delayed_writes.empty());
}

TEST_F(NodeWriterTest, delayed_write_across_chunk_boundary)
{
    // Fill up to near end of a chunk so the next large write must go
    // to a new chunk via allocate_write_offset
    auto const near_end = chunk_size - 1024;
    node_writer_append_dummy_bytes(aux.writer_fast.node_writer, near_end);

    auto const chunk_id_before =
        aux.writer_fast.write_position.current_chunk_id;

    // Write a node larger than remaining chunk space - forces new chunk
    // allocation via the delayed write path
    unsigned const large_node_size = 2048;
    auto large_node = make_node_of_size(large_node_size);
    auto const offset = async_write_node_set_spare(aux, large_node, true);

    // Should be allocated at start of a new chunk
    EXPECT_EQ(offset.offset, 0u);
    EXPECT_NE(offset.id, chunk_id_before);

    // The new chunk must be in the fast list
    EXPECT_TRUE(aux.db_metadata()->at(offset.id)->in_fast_list);

    // Flush and verify queue drained
    aux.io->flush();
    EXPECT_TRUE(aux.writer_fast.delayed_writes.empty());
}

TEST_F(NodeWriterTest, write_position_tracks_through_delayed_writes)
{
    unsigned const node_disk_size = 1024;
    auto node = make_node_of_size(node_disk_size);
    unsigned const num_nodes =
        AsyncIO::MONAD_IO_BUFFERS_WRITE_SIZE / node_disk_size;

    // Record initial write_position
    auto const initial_chunk = aux.writer_fast.write_position.current_chunk_id;
    auto const initial_offset = aux.writer_fast.write_position.current_offset;
    EXPECT_EQ(initial_offset, 0u);

    // Write nodes that fit in buffer (fast path) - write_position advances
    for (unsigned i = 0; i < num_nodes; ++i) {
        async_write_node_set_spare(aux, node, true);
    }
    EXPECT_EQ(aux.writer_fast.write_position.current_chunk_id, initial_chunk);
    EXPECT_EQ(
        aux.writer_fast.write_position.current_offset,
        (file_offset_t)num_nodes * node_disk_size);

    // Now write a node that triggers delayed path
    unsigned const large_node_size = node_disk_size * 2;
    auto large_node = make_node_of_size(large_node_size);
    auto const pos_before_delayed =
        aux.writer_fast.write_position.current_offset;
    async_write_node_set_spare(aux, large_node, true);

    // write_position must have advanced even though write is delayed
    EXPECT_EQ(
        aux.writer_fast.write_position.current_offset,
        pos_before_delayed + large_node_size);
}

TEST_F(NodeWriterTest, flush_after_delayed_writes_produces_valid_state)
{
    unsigned const node_disk_size = 1024;
    auto node = make_node_of_size(node_disk_size);

    // Write enough to trigger a delayed write
    unsigned const num_nodes =
        AsyncIO::MONAD_IO_BUFFERS_WRITE_SIZE / node_disk_size;
    for (unsigned i = 0; i < num_nodes; ++i) {
        async_write_node_set_spare(aux, node, true);
    }
    ASSERT_EQ(
        aux.writer_fast.node_writer->sender().remaining_buffer_bytes(), 0);

    // Queue delayed writes
    unsigned const large_node_size = node_disk_size * 2;
    auto large_node = make_node_of_size(large_node_size);
    async_write_node_set_spare(aux, large_node, true);
    async_write_node_set_spare(aux, large_node, true);

    // Use write_new_root_node which calls flush_buffered_writes internally
    auto root_node = make_node_of_size(node_disk_size);
    auto const root_offset = write_new_root_node(aux, root_node, 1);

    // Root offset should be valid
    EXPECT_TRUE(aux.db_metadata()->at(root_offset.id)->in_fast_list);

    // All delayed writes must have been drained by flush
    EXPECT_TRUE(aux.writer_fast.delayed_writes.empty());
    EXPECT_TRUE(aux.writer_slow.delayed_writes.empty());
}

TEST_F(NodeWriterTest, delayed_written_nodes_can_be_read_back)
{
    unsigned const node_disk_size = 1024;
    auto small_node = make_node_of_size(node_disk_size);
    unsigned const num_nodes =
        AsyncIO::MONAD_IO_BUFFERS_WRITE_SIZE / node_disk_size;

    // Fill buffer completely so subsequent writes go through delayed path
    for (unsigned i = 0; i < num_nodes; ++i) {
        async_write_node_set_spare(aux, small_node, true);
    }
    ASSERT_EQ(
        aux.writer_fast.node_writer->sender().remaining_buffer_bytes(), 0);

    // Write nodes of different sizes through the delayed path, track offsets
    unsigned const sizes[] = {1024, 2048, 4096, 1536};
    std::vector<std::pair<chunk_offset_t, Node::SharedPtr>> written_nodes;
    for (auto sz : sizes) {
        auto node = make_node_of_size(sz);
        auto offset = async_write_node_set_spare(aux, node, true);
        written_nodes.emplace_back(offset, node);
    }

    // Flush everything to disk and register a version
    auto root = make_node_of_size(node_disk_size);
    auto const root_offset = write_new_root_node(aux, root, 1);
    ASSERT_TRUE(aux.writer_fast.delayed_writes.empty());

    // Read back each delayed-written node and verify data integrity
    for (auto const &[offset, original_node] : written_nodes) {
        auto read_back = read_node_blocking(aux, offset, 1);
        ASSERT_NE(read_back, nullptr)
            << "Failed to read node at chunk=" << offset.id
            << " offset=" << offset.offset;
        EXPECT_EQ(read_back->get_disk_size(), original_node->get_disk_size());
        EXPECT_EQ(read_back->value(), original_node->value());
    }

    // Also verify the root node
    auto root_read_back = read_node_blocking(aux, root_offset, 1);
    ASSERT_NE(root_read_back, nullptr);
    EXPECT_EQ(root_read_back->get_disk_size(), root->get_disk_size());
    EXPECT_EQ(root_read_back->value(), root->value());
}

TEST_F(NodeWriterTest, delayed_write_node_spanning_multiple_buffers)
{
    // Create a node larger than WRITE_BUFFER_SIZE (8MB) so that when
    // process_delayed_writes serializes it, the node must span multiple
    // I/O buffers, exercising the inner loop's buffer-replacement path.
    unsigned const large_node_size =
        AsyncIO::MONAD_IO_BUFFERS_WRITE_SIZE + 1024 * 1024; // 9MB
    auto large_node = make_node_of_size(large_node_size);

    unsigned const small_size = 1024;
    auto small_node = make_node_of_size(small_size);
    unsigned const num_nodes =
        AsyncIO::MONAD_IO_BUFFERS_WRITE_SIZE / small_size;

    // Fill buffer completely to force delayed path
    for (unsigned i = 0; i < num_nodes; ++i) {
        async_write_node_set_spare(aux, small_node, true);
    }
    ASSERT_EQ(
        aux.writer_fast.node_writer->sender().remaining_buffer_bytes(), 0);

    // Write the large node — must be queued as delayed
    auto const offset = async_write_node_set_spare(aux, large_node, true);

    // Flush to disk and register version
    auto root = make_node_of_size(small_size);
    (void)write_new_root_node(aux, root, 1);
    EXPECT_TRUE(aux.writer_fast.delayed_writes.empty());

    // Read back the large node and verify integrity
    auto read_back = read_node_blocking(aux, offset, 1);
    ASSERT_NE(read_back, nullptr);
    EXPECT_EQ(read_back->get_disk_size(), large_node->get_disk_size());
    EXPECT_EQ(read_back->value(), large_node->value());
}

// --- Non-blocking buffer exhaustion tests ---
//
// With 4 write buffers total (fast holds 1, slow holds 1, 2 free), writing
// a node larger than 3 * WRITE_BUFFER_SIZE inside process_delayed_writes
// deterministically exhausts all available buffers: the initial full buffer
// plus the 2 free ones are consumed (submitted to io_uring), leaving
// node_writer null with offset_in_data pointing mid-node.
// No polling occurs inside process_delayed_writes, so this is race-free.

TEST_F(NodeWriterTest, async_write_node_queues_when_node_writer_null)
{
    unsigned const small_size = 1024;
    auto small_node = make_node_of_size(small_size);
    unsigned const num_nodes =
        AsyncIO::MONAD_IO_BUFFERS_WRITE_SIZE / small_size;

    // Fill fast buffer completely
    for (unsigned i = 0; i < num_nodes; ++i) {
        async_write_node_set_spare(aux, small_node, true);
    }
    ASSERT_EQ(
        aux.writer_fast.node_writer->sender().remaining_buffer_bytes(), 0);

    // Write a node spanning >3 buffers. process_delayed_writes will consume
    // all 3 available write buffers (current full + 2 free) and fail to
    // allocate a 4th (held by slow writer), leaving node_writer null.
    unsigned const huge_node_size =
        3 * AsyncIO::MONAD_IO_BUFFERS_WRITE_SIZE + 1024 * 1024;
    auto huge_node = make_node_of_size(huge_node_size);
    async_write_node_set_spare(aux, huge_node, true);

    // node_writer should be null (all buffers in flight or held by slow)
    ASSERT_EQ(aux.writer_fast.node_writer, nullptr);

    // Now write another small node — must be queued because node_writer is null
    auto const queued_offset =
        async_write_node_set_spare(aux, small_node, true);

    // The small node should be in the delayed writes queue
    // (it was appended because !node_writer)
    bool found = false;
    for (auto const &dw : aux.writer_fast.delayed_writes) {
        if (dw.allocated_offset.id == queued_offset.id &&
            dw.allocated_offset.offset == queued_offset.offset) {
            found = true;
            break;
        }
    }
    EXPECT_TRUE(found) << "Small node not found in delayed_writes queue";

    // write_position should have advanced for both the huge and small nodes
    EXPECT_GE(
        aux.writer_fast.write_position.current_offset,
        queued_offset.offset + small_size);

    // Drain and verify everything completes
    drain_delayed_writes(true);
    EXPECT_TRUE(aux.writer_fast.delayed_writes.empty());
}

TEST_F(NodeWriterTest, buffer_exhaustion_increments_alloc_failure_counter)
{
    unsigned const small_size = 1024;
    auto small_node = make_node_of_size(small_size);
    unsigned const num_nodes =
        AsyncIO::MONAD_IO_BUFFERS_WRITE_SIZE / small_size;

    // Fill fast buffer completely
    for (unsigned i = 0; i < num_nodes; ++i) {
        async_write_node_set_spare(aux, small_node, true);
    }

    auto const failures_before = aux.writer_fast.buffer_alloc_failures;

    // Write a huge node that exhausts all available write buffers
    unsigned const huge_node_size =
        3 * AsyncIO::MONAD_IO_BUFFERS_WRITE_SIZE + 1024 * 1024;
    auto huge_node = make_node_of_size(huge_node_size);
    async_write_node_set_spare(aux, huge_node, true);

    // buffer_alloc_failures must have been incremented
    EXPECT_GT(aux.writer_fast.buffer_alloc_failures, failures_before);

    // delayed_writes must be non-empty (partially written node remains)
    EXPECT_FALSE(aux.writer_fast.delayed_writes.empty());

    // Drain via I/O completions and verify everything finishes
    drain_delayed_writes(true);
    EXPECT_TRUE(aux.writer_fast.delayed_writes.empty());
}

TEST_F(NodeWriterTest, process_delayed_writes_resumes_partial_node)
{
    unsigned const small_size = 1024;
    auto small_node = make_node_of_size(small_size);
    unsigned const num_nodes =
        AsyncIO::MONAD_IO_BUFFERS_WRITE_SIZE / small_size;

    // Fill fast buffer completely
    for (unsigned i = 0; i < num_nodes; ++i) {
        async_write_node_set_spare(aux, small_node, true);
    }

    // Write a huge node (>3 buffers). process_delayed_writes writes 3 buffers
    // worth (~24MB), then fails to allocate a 4th. The node remains in the
    // queue with offset_in_data pointing to the resume position.
    unsigned const huge_node_size =
        3 * AsyncIO::MONAD_IO_BUFFERS_WRITE_SIZE + 1024 * 1024;
    auto huge_node = make_node_of_size(huge_node_size);
    auto const offset = async_write_node_set_spare(aux, huge_node, true);

    // Verify partial progress: front of queue should have offset_in_data > 0
    ASSERT_FALSE(aux.writer_fast.delayed_writes.empty());
    auto const &front = aux.writer_fast.delayed_writes.front();
    EXPECT_GT(front.offset_in_data, 0u);
    EXPECT_LT(front.offset_in_data, huge_node_size);

    // Resume position must be disk-page aligned (we only pause at buffer
    // boundaries, which are always disk-page aligned)
    EXPECT_EQ(front.offset_in_data % DISK_PAGE_SIZE, 0u);

    // Drain — I/O completions free buffers, process_delayed_writes resumes
    // from offset_in_data and finishes the node
    drain_delayed_writes(true);
    EXPECT_TRUE(aux.writer_fast.delayed_writes.empty());

    // Verify the node can be read back correctly
    auto root = make_node_of_size(small_size);
    (void)write_new_root_node(aux, root, 1);

    auto read_back = read_node_blocking(aux, offset, 1);
    ASSERT_NE(read_back, nullptr);
    EXPECT_EQ(read_back->get_disk_size(), huge_node->get_disk_size());
    EXPECT_EQ(read_back->value(), huge_node->value());
}

TEST_F(NodeWriterTest, io_completion_triggers_delayed_write_drain)
{
    unsigned const small_size = 1024;
    auto small_node = make_node_of_size(small_size);
    unsigned const num_nodes =
        AsyncIO::MONAD_IO_BUFFERS_WRITE_SIZE / small_size;

    // Fill fast buffer completely
    for (unsigned i = 0; i < num_nodes; ++i) {
        async_write_node_set_spare(aux, small_node, true);
    }

    // Queue several distinct delayed writes that each fill a buffer
    unsigned const big_size = AsyncIO::MONAD_IO_BUFFERS_WRITE_SIZE + small_size;
    auto big_node = make_node_of_size(big_size);

    async_write_node_set_spare(aux, big_node, true);
    async_write_node_set_spare(aux, big_node, true);
    async_write_node_set_spare(aux, big_node, true);

    // Some writes should be pending (buffers exhausted)
    auto const initial_queue_size = aux.writer_fast.delayed_writes.size();

    // Poll one I/O at a time — each completion should trigger
    // process_delayed_writes via write_operation_io_receiver::set_value,
    // draining more items from the queue
    size_t prev_size = initial_queue_size;
    unsigned polls = 0;
    while (!aux.writer_fast.delayed_writes.empty()) {
        aux.io->poll_blocking(1);
        ++polls;
        // Queue should be monotonically non-increasing
        EXPECT_LE(aux.writer_fast.delayed_writes.size(), prev_size);
        prev_size = aux.writer_fast.delayed_writes.size();
    }

    EXPECT_TRUE(aux.writer_fast.delayed_writes.empty());
    // Verify that at least one poll was needed (drain wasn't instant)
    EXPECT_GT(polls, 0u);
}

TEST_F(NodeWriterTest, ensure_writer_at_offset_creates_from_null)
{
    unsigned const small_size = 1024;
    auto small_node = make_node_of_size(small_size);
    unsigned const num_nodes =
        AsyncIO::MONAD_IO_BUFFERS_WRITE_SIZE / small_size;

    // Fill fast buffer completely
    for (unsigned i = 0; i < num_nodes; ++i) {
        async_write_node_set_spare(aux, small_node, true);
    }

    // Exhaust all write buffers to get node_writer to null
    unsigned const huge_node_size =
        3 * AsyncIO::MONAD_IO_BUFFERS_WRITE_SIZE + 1024 * 1024;
    auto huge_node = make_node_of_size(huge_node_size);
    async_write_node_set_spare(aux, huge_node, true);
    ASSERT_EQ(aux.writer_fast.node_writer, nullptr);

    // Free one buffer by completing one I/O
    aux.io->poll_blocking(1);

    // After I/O completion, the callback should have re-created node_writer
    // via process_delayed_writes -> ensure_writer_at_offset (null path)
    // The delayed queue should have made progress
    EXPECT_LT(aux.writer_fast.delayed_writes.size(), static_cast<size_t>(2))
        << "Queue should have made progress after I/O completion";

    // Drain remaining
    drain_delayed_writes(true);
    EXPECT_TRUE(aux.writer_fast.delayed_writes.empty());
}

TEST_F(NodeWriterTest, interleaved_fast_and_slow_delayed_writes)
{
    unsigned const small_size = 1024;
    auto small_node = make_node_of_size(small_size);
    unsigned const num_nodes =
        AsyncIO::MONAD_IO_BUFFERS_WRITE_SIZE / small_size;

    // Fill both fast and slow buffers completely so that subsequent
    // writes trigger the delayed write path for both writers.
    for (unsigned i = 0; i < num_nodes; ++i) {
        async_write_node_set_spare(aux, small_node, true);
    }
    ASSERT_EQ(
        aux.writer_fast.node_writer->sender().remaining_buffer_bytes(), 0);

    for (unsigned i = 0; i < num_nodes; ++i) {
        async_write_node_set_spare(aux, small_node, false);
    }
    ASSERT_EQ(
        aux.writer_slow.node_writer->sender().remaining_buffer_bytes(), 0);

    // Write nodes larger than remaining buffer through both the fast and
    // slow delayed write paths. Each write triggers process_delayed_writes
    // which submits the full buffer and allocates a replacement.
    unsigned const big_size = small_size * 4;
    auto big_node = make_node_of_size(big_size);

    std::vector<std::pair<chunk_offset_t, bool>> written_nodes;

    // Interleave fast and slow writes
    for (int i = 0; i < 4; ++i) {
        auto fast_off = async_write_node_set_spare(aux, big_node, true);
        written_nodes.emplace_back(fast_off, true);
        auto slow_off = async_write_node_set_spare(aux, big_node, false);
        written_nodes.emplace_back(slow_off, false);
    }

    // Verify offsets are in the correct lists (is_fast flag propagation)
    for (auto const &[off, is_fast] : written_nodes) {
        if (is_fast) {
            EXPECT_TRUE(aux.db_metadata()->at(off.id)->in_fast_list)
                << "Fast node at chunk " << off.id << " not in fast list";
        }
        else {
            EXPECT_TRUE(aux.db_metadata()->at(off.id)->in_slow_list)
                << "Slow node at chunk " << off.id << " not in slow list";
        }
    }

    // write_position should have advanced for both writers
    EXPECT_GT(aux.writer_fast.write_position.current_offset, 0u);
    EXPECT_GT(aux.writer_slow.write_position.current_offset, 0u);

    // Flush everything via write_new_root_node and verify both queues drain
    auto root = make_node_of_size(small_size);
    auto const root_offset = write_new_root_node(aux, root, 1);
    EXPECT_TRUE(aux.writer_fast.delayed_writes.empty());
    EXPECT_TRUE(aux.writer_slow.delayed_writes.empty());

    // Read back all nodes and verify data integrity
    for (auto const &[off, is_fast] : written_nodes) {
        auto read_back = read_node_blocking(aux, off, 1);
        ASSERT_NE(read_back, nullptr)
            << "Failed to read node at chunk=" << off.id
            << " offset=" << off.offset << " is_fast=" << is_fast;
        EXPECT_EQ(read_back->get_disk_size(), big_node->get_disk_size());
        EXPECT_EQ(read_back->value(), big_node->value());
    }

    // Verify root node
    auto root_read = read_node_blocking(aux, root_offset, 1);
    ASSERT_NE(root_read, nullptr);
    EXPECT_EQ(root_read->get_disk_size(), root->get_disk_size());
}
