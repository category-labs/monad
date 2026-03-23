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

#include "test_fixtures_base.hpp"
#include "test_fixtures_gtest.hpp"

#include <category/core/assert.h>
#include <category/core/byte_string.hpp>
#include <category/core/small_prng.hpp>
#include <category/mpt/node.hpp>
#include <category/mpt/traverse.hpp>
#include <category/mpt/trie.hpp>
#include <category/mpt/update.hpp>
#include <category/mpt/util.hpp>

#include <category/core/test_util/gtest_signal_stacktrace_printer.hpp> // NOLINT

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
                        0x1234567812345678123456781234567812345678123456781234567812345678_bytes);
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
                aux.writer_fast.node_writer->sender().offset().offset >=
                    chunk_inner_offset_fast &&
                count_slow >= slow_chunks &&
                aux.writer_slow.node_writer->sender().offset().offset >=
                    chunk_inner_offset_slow) {
                break;
            }
        }
    };
    ensure_total_bytes_written(0, eightMB, 0, eightMB);

    auto const trie_min_offsets = calc_min_offsets(*this->root);
    EXPECT_EQ(trie_min_offsets.fast, 0);
    EXPECT_EQ(trie_min_offsets.slow, 0);

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
            compact_offset_pair test_min_offsets{};
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
            compact_offset_pair node_offsets;
            if (virtual_node_offset.in_fast_list()) {
                node_offsets.fast =
                    compact_virtual_chunk_offset_t{virtual_node_offset};
            }
            else {
                node_offsets.slow =
                    compact_virtual_chunk_offset_t{virtual_node_offset};
            }
            root_to_node_records.push({&node, node_offsets});
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
                auto const expected_min_offsets = calc_min_offsets(
                    *const_cast<Node *>(&node),
                    aux.physical_to_virtual(aux.get_latest_root_offset()));
                EXPECT_EQ(node_record.test_min_offsets, expected_min_offsets);
            }
            else {
                auto &parent_record = root_to_node_records.top();
                Node *const parent = const_cast<Node *>(parent_record.node);
                auto const stored_min_offsets = parent->min_offsets(
                    parent->to_child_index(branch_in_parent));
                // verify that min offset stored in parent equals the calculated
                // one during traversal
                EXPECT_EQ(stored_min_offsets, node_record.test_min_offsets);

                // update parent record.
                parent_record.test_min_offsets.fast = std::min(
                    parent_record.test_min_offsets.fast,
                    node_record.test_min_offsets.fast);
                parent_record.test_min_offsets.slow = std::min(
                    parent_record.test_min_offsets.slow,
                    node_record.test_min_offsets.slow);
            }
        }

        virtual std::unique_ptr<TraverseMachine> clone() const override
        {
            return std::make_unique<
                TraverseCalculateAndVerifyMinTruncatedOffsets>(*this);
        }

    } traverse{aux};

    // WARNING: test will fail and there are memory leak using parallel traverse
    ASSERT_TRUE(preorder_traverse_blocking(aux, *root, traverse, block_id));
    EXPECT_EQ(traverse.level, 0);
    EXPECT_EQ(traverse.root_to_node_records.empty(), true);
}
