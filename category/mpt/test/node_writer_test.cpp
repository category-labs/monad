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
#include <category/mpt/fiber_write_utils.hpp>
#include <category/mpt/node.hpp>
#include <category/mpt/trie.hpp>

#include <boost/fiber/fiber.hpp>
#include <boost/fiber/operations.hpp>

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

    // Run test code in a fiber context with completion polling.
    // This is required for fiber-based writes which yield and expect
    // completions to be polled.
    template <typename F>
    void run_in_fiber_context(F &&test_func)
    {
        aux.setup_fiber_write_buffers();

        bool done = false;
        boost::fibers::fiber test_fiber([&]() {
            test_func();
            done = true;
        });

        // Hot loop: poll completions and run fiber scheduler until done
        while (!done) {
            poll_ring_completions(io.write_ring());
            poll_ring_completions(io.read_ring());
            boost::this_fiber::yield();
        }

        test_fiber.join();
        aux.release_fiber_write_buffers();
    }

    uint32_t get_fiber_buffer_chunk_id()
    {
        return aux.fiber_write_buffer_fast_ref().current_offset().id;
    }
};

using NodeWriterTest = NodeWriterTestBase<>;

TEST_F(NodeWriterTest, write_nodes_each_within_buffer)
{
    run_in_fiber_context([&]() {
        auto const initial_chunk_id = get_fiber_buffer_chunk_id();

        unsigned const node_disk_size = 1024;
        unsigned const num_nodes =
            AsyncIO::MONAD_IO_BUFFERS_WRITE_SIZE / node_disk_size;
        auto node = make_node_of_size(node_disk_size);

        // Write multiple nodes that should all fit in one buffer
        for (unsigned i = 0; i < num_nodes; ++i) {
            auto const node_offset = async_write_node_set_spare(aux, *node, true);
            EXPECT_EQ(node_offset.offset, node_disk_size * i);
            EXPECT_EQ(node_offset.id, initial_chunk_id);
            EXPECT_EQ(
                aux.fiber_write_buffer_fast_ref().written_bytes(),
                node_offset.offset + node_disk_size);
        }

        // Buffer should be full
        EXPECT_EQ(aux.fiber_write_buffer_fast_ref().remaining(), 0);

        // Write one more node - buffer will flush and start fresh
        auto const node_offset = async_write_node_set_spare(aux, *node, true);
        // After flush, new write starts at buffer offset after the flush
        EXPECT_EQ(node_offset.offset, AsyncIO::MONAD_IO_BUFFERS_WRITE_SIZE);
        EXPECT_EQ(node_offset.id, initial_chunk_id);
        EXPECT_EQ(
            aux.fiber_write_buffer_fast_ref().written_bytes(), node_disk_size);
    });
}

TEST_F(NodeWriterTest, write_node_at_new_chunk)
{
    run_in_fiber_context([&]() {
        // Write nodes until we're near a chunk boundary, then write a node
        // that's too big to fit - it should go to a new chunk.
        auto const initial_chunk_id = get_fiber_buffer_chunk_id();

        // First, fill up most of the chunk with small writes
        unsigned const small_node_size = 4096;
        auto small_node = make_node_of_size(small_node_size);

        // Write nodes until we're close to chunk capacity
        size_t total_written = 0;
        auto const chunk_capacity = io.chunk_capacity(initial_chunk_id);
        while (total_written + small_node_size * 2 < chunk_capacity) {
            auto const offset = async_write_node_set_spare(aux, *small_node, true);
            total_written = offset.offset + small_node_size;
        }

        // Now write a large node that won't fit in remaining space
        auto const remaining = chunk_capacity - total_written;
        auto large_node = make_node_of_size(static_cast<unsigned>(remaining + 1024));
        auto const large_offset = async_write_node_set_spare(aux, *large_node, true);

        // The large node should be written to a new chunk
        EXPECT_NE(large_offset.id, initial_chunk_id);
        EXPECT_EQ(large_offset.offset, 0); // Start of new chunk
    });
}
