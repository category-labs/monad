#include "test_fixtures_base.hpp"
#include "test_fixtures_gtest.hpp"

#include <monad/core/assert.h>
#include <monad/core/byte_string.hpp>
#include <monad/core/hex_literal.hpp>
#include <monad/core/small_prng.hpp>
#include <monad/mpt/node.hpp>
#include <monad/mpt/traverse.hpp>
#include <monad/mpt/trie.hpp>
#include <monad/mpt/update.hpp>
#include <monad/mpt/util.hpp>

#include <monad/test/gtest_signal_stacktrace_printer.hpp> // NOLINT

#include <algorithm>
#include <atomic>
#include <cstddef>
#include <cstdint>
#include <memory>
#include <stack>
#include <utility>
#include <vector>

using namespace ::monad::test;
using namespace ::monad::mpt;

TEST_F(OnDiskMerkleTrieGTest, min_truncated_offsets)
{
    this->sm = std::make_unique<StateMachineAlways<MerkleCompute>>();

    this->aux.alternate_slow_fast_node_writer_unit_testing_only(true);
    constexpr size_t const eightMB = 8 * 1024 * 1024;

    uint64_t const block_id = 0;
    // ensure total bytes written on both fast and slow lists
    auto ensure_total_bytes_written = [&](size_t fast_chunks,
                                          size_t chunk_inner_offset_fast,
                                          size_t slow_chunks,
                                          size_t chunk_inner_offset_slow) {
        monad::small_prng rand;
        std::vector<std::pair<monad::byte_string, size_t>> keys;

        std::vector<Update> updates;
        updates.reserve(1000);
        for (;;) {
            UpdateList update_ls;
            updates.clear();
            for (size_t n = 0; n < 1000; n++) {
                {
                    monad::byte_string key(
                        0x1234567812345678123456781234567812345678123456781234567812345678_hex);
                    for (size_t n = 0; n < key.size(); n += 4) {
                        *(uint32_t *)(key.data() + n) = rand();
                    }
                    keys.emplace_back(
                        std::move(key), aux.get_latest_root_offset().id);
                }
                updates.push_back(
                    make_update(keys.back().first, keys.back().first));
                update_ls.push_front(updates.back());
            }
            root = upsert(
                aux, block_id, *sm, std::move(root), std::move(update_ls));
            size_t count_fast = 0;
            for (auto const *ci = aux.db_metadata()->fast_list_begin();
                 ci != nullptr;
                 count_fast++, ci = ci->next(aux.db_metadata())) {
            }
            size_t count_slow = 0;
            for (auto const *ci = aux.db_metadata()->slow_list_begin();
                 ci != nullptr;
                 count_slow++, ci = ci->next(aux.db_metadata())) {
            }
            if (count_fast >= fast_chunks &&
                aux.node_writer_fast->sender().offset().offset >=
                    chunk_inner_offset_fast &&
                count_slow >= slow_chunks &&
                aux.node_writer_slow->sender().offset().offset >=
                    chunk_inner_offset_slow) {
                break;
            }
        }
    };
    ensure_total_bytes_written(0, eightMB, 0, eightMB);

    auto [trie_min_offset_fast, trie_min_offset_slow] =
        calc_min_offsets(*this->root);
    EXPECT_EQ(trie_min_offset_fast, 0);
    EXPECT_EQ(trie_min_offset_slow, 0);

    struct TraverseCalculateAndVerifyMinTruncatedOffsets
        : public TraverseMachine
    {
        UpdateAuxImpl &aux; // for chunk count lookup
        size_t level{0};

        struct traverse_record_t
        {
            Node const *node{nullptr};
            // record the calculated min truncated inorder offsets of trie
            // rooted at node in traversal
            compact_virtual_chunk_offset_t test_min_offset_fast{
                INVALID_COMPACT_VIRTUAL_OFFSET};
            compact_virtual_chunk_offset_t test_min_offset_slow{
                INVALID_COMPACT_VIRTUAL_OFFSET};
        };

        std::stack<traverse_record_t> root_to_node_records;

        explicit TraverseCalculateAndVerifyMinTruncatedOffsets(
            UpdateAuxImpl &aux)
            : aux(aux)
        {
        }

        virtual bool
        down(unsigned char const branch_in_parent, Node const &node) override
        {
            ++level; // increment level counter

            if (root_to_node_records.empty()) { // indicates node is root
                root_to_node_records.push(traverse_record_t{.node = &node});
                return true;
            }
            Node *const parent =
                const_cast<Node *>(root_to_node_records.top().node);
            MONAD_ASSERT(parent != nullptr);
            auto const node_offset =
                parent->fnext(parent->to_child_index(branch_in_parent));
            auto const virtual_node_offset =
                aux.physical_to_virtual(node_offset);
            MONAD_ASSERT(virtual_node_offset.has_value());
            if (virtual_node_offset->in_fast_list()) {
                root_to_node_records.push(
                    {&node,
                     compact_virtual_chunk_offset_t{*virtual_node_offset},
                     INVALID_COMPACT_VIRTUAL_OFFSET});
            }
            else {
                root_to_node_records.push(
                    {&node,
                     INVALID_COMPACT_VIRTUAL_OFFSET,
                     compact_virtual_chunk_offset_t{*virtual_node_offset}});
            }
            return true;
        }

        virtual void
        up(unsigned char const branch_in_parent, Node const &node) override
        {
            --level;

            auto const node_record = root_to_node_records.top();
            root_to_node_records.pop();
            if (root_to_node_records.empty()) { // node is root
                // verify that offset equals calculated one in traversal
                auto const virtual_root_offset =
                    aux.physical_to_virtual(aux.get_latest_root_offset());
                MONAD_ASSERT(virtual_root_offset.has_value());
                auto [node_branch_min_fast_off, node_branch_min_slow_off] =
                    calc_min_offsets(
                        *const_cast<Node *>(&node),
                        virtual_root_offset.value());
                EXPECT_EQ(
                    node_record.test_min_offset_fast, node_branch_min_fast_off);
                EXPECT_EQ(
                    node_record.test_min_offset_slow, node_branch_min_slow_off);
            }
            else {
                auto &parent_record = root_to_node_records.top();
                Node *const parent = const_cast<Node *>(parent_record.node);
                auto const node_branch_min_fast_off = parent->min_offset_fast(
                    parent->to_child_index(branch_in_parent));
                auto const node_branch_min_slow_off = parent->min_offset_slow(
                    parent->to_child_index(branch_in_parent));
                // verify that min offset stored in parent equals the calculated
                // one during traversal
                EXPECT_EQ(
                    node_branch_min_fast_off, node_record.test_min_offset_fast);
                EXPECT_EQ(
                    node_branch_min_slow_off, node_record.test_min_offset_slow);

                // update parent record.
                parent_record.test_min_offset_fast = std::min(
                    parent_record.test_min_offset_fast,
                    node_record.test_min_offset_fast);
                parent_record.test_min_offset_slow = std::min(
                    parent_record.test_min_offset_slow,
                    node_record.test_min_offset_slow);
            }
        }

        virtual std::unique_ptr<TraverseMachine> clone() const override
        {
            return std::make_unique<
                TraverseCalculateAndVerifyMinTruncatedOffsets>(*this);
        }

    } traverse{this->aux};

    // WARNING: test will fail and there are memory leak using parallel traverse
    ASSERT_TRUE(
        preorder_traverse_blocking(this->aux, *this->root, traverse, block_id));
    EXPECT_EQ(traverse.level, 0);
    EXPECT_EQ(traverse.root_to_node_records.empty(), true);
}
