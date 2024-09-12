#include "test_fixtures_base.hpp"
#include "test_fixtures_gtest.hpp"

#include <monad/core/assert.h>

#include <monad/async/config.hpp>
#include <monad/mpt/config.hpp>
#include <monad/mpt/node.hpp>
#include <monad/mpt/trie.hpp>
#include <monad/test/gtest_signal_stacktrace_printer.hpp> // NOLINT

#include <cstddef>
#include <cstdint>

using namespace MONAD_MPT_NAMESPACE;
using namespace MONAD_ASYNC_NAMESPACE;
using namespace monad::literals;

static constexpr size_t CHUNKS_TO_FILL = 3;

// Note that storage pool is configured with 8MB storage chunks
struct NodeWriterTest
    : public monad::test::FillDBWithChunksGTest<
          monad::test::FillDBWithChunksConfig{.chunks_to_fill = CHUNKS_TO_FILL}>
{
private:
    uint32_t rewind_fast_list_(unsigned const remaining_bytes_in_chunk)
    {
        auto const fast_chunk_ids = state()->fast_list_ids();
        EXPECT_TRUE(fast_chunk_ids.size() >= 2);

        // rewind to close to the end of second to last fast chunk in use
        auto const insertion_index = fast_chunk_ids.size() - 2;
        auto const rewind_chunk_id = fast_chunk_ids[insertion_index].first;
        auto chunk = state()->io.storage_pool().chunk(
            storage_pool::seq, rewind_chunk_id);
        auto const fast_offset_rewind_to = chunk_offset_t{
            rewind_chunk_id, chunk->size() - remaining_bytes_in_chunk};

        // reset fast offset to close to the end of last chunk
        state()->aux.advance_db_offsets_to(
            fast_offset_rewind_to, state()->aux.get_start_of_wip_slow_offset());
        state()->aux.append_root_offset(INVALID_OFFSET);
        state()->aux.rewind_to_match_offsets();

        EXPECT_EQ(
            state()->aux.node_writer_fast->sender().offset(),
            fast_offset_rewind_to);
        uint32_t const curr_node_writer_chunk_id =
            state()->aux.node_writer_fast->sender().offset().id;
        EXPECT_EQ(
            state()
                ->aux.db_metadata()
                ->at(curr_node_writer_chunk_id)
                ->insertion_count(),
            insertion_index);
        return curr_node_writer_chunk_id;
    }

    Node::UniquePtr make_node_of_size(unsigned const node_disk_size)
    {
        MONAD_ASSERT(node_disk_size > sizeof(Node) + Node::disk_size_bytes);
        auto const node_value_size =
            node_disk_size - sizeof(Node) - Node::disk_size_bytes;
        auto const value = monad::byte_string(node_value_size, 0xf);
        auto node = make_node(0, {}, {}, value, {}, 0);
        return node;
    }

public:
    void rewind_then_write_node(
        unsigned const remaining_bytes_in_chunk, unsigned node_disk_size)
    {
        auto const curr_node_writer_chunk_id =
            rewind_fast_list_(remaining_bytes_in_chunk);
        auto node = make_node_of_size(node_disk_size);
        EXPECT_EQ(node->get_disk_size(), node_disk_size);
        auto const chunks_before = state()->fast_list_ids().size();
        // write node
        auto const node_offset =
            async_write_node_set_spare(state()->aux, *node, true);
        if (node->get_disk_size() > remaining_bytes_in_chunk) {
            // Node will be written to the start of next chunk
            auto &new_node_writer = state()->aux.node_writer_fast;
            uint32_t const new_node_writer_chunk_id =
                new_node_writer->sender().offset().id;
            EXPECT_EQ(node_offset.id, new_node_writer_chunk_id);
            EXPECT_EQ(node_offset.offset, 0);
            EXPECT_EQ(new_node_writer->sender().offset().offset, 0);
            // new node writer offset should start at the next chunk
            EXPECT_NE(new_node_writer_chunk_id, curr_node_writer_chunk_id);
            EXPECT_EQ(
                (uint32_t)state()
                    ->aux.db_metadata()
                    ->at(new_node_writer_chunk_id)
                    ->insertion_count(),
                (uint32_t)state()
                        ->aux.db_metadata()
                        ->at(curr_node_writer_chunk_id)
                        ->insertion_count() +
                    1);
            EXPECT_EQ(chunks_before + 1, state()->fast_list_ids().size());
        }
        else {
            // Node will be appended to the existing chunk
            EXPECT_EQ(node_offset.id, curr_node_writer_chunk_id);
            EXPECT_EQ(chunks_before, state()->fast_list_ids().size());
        }
    }
};

TEST_F(NodeWriterTest, write_node)
{
    // remaining bytes < node size: write node to next chunk
    rewind_then_write_node(2 * 1024 * 1024, 5 * 1024 * 1024);

    // reminaing bytes > node size: write node to existing chunk
    rewind_then_write_node(5 * 1024 * 1024, 2 * 1024 * 1024);
}

TEST_F(NodeWriterTest, replace_fast_writer_at_chunk_boundary)
{
    unsigned const node_disk_size = 1024;
    // After this line, node writer is at the end of a chunk
    rewind_then_write_node(node_disk_size, node_disk_size);

    auto const new_writer_offset =
        state()->aux.node_writer_fast->sender().offset();
    EXPECT_EQ(
        new_writer_offset.offset + node_disk_size,
        state()->aux.io->chunk_capacity(new_writer_offset.id));

    // Replace fast node writer, writer should start at a new chunk that belongs
    // to fast list
    auto new_node_writer =
        replace_node_writer(state()->aux, state()->aux.node_writer_fast);
    EXPECT_EQ(new_node_writer->sender().offset().offset, 0);
    EXPECT_NE(new_writer_offset.id, new_node_writer->sender().offset().id);
    EXPECT_TRUE(state()
                    ->aux.db_metadata()
                    ->at(new_node_writer->sender().offset().id)
                    ->in_fast_list);
}
