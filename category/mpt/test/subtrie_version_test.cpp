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
#include <category/mpt/node.hpp>
#include <category/mpt/traverse.hpp>
#include <category/mpt/trie.hpp>
#include <category/mpt/update.hpp>
#include <category/mpt/util.hpp>

#include <category/core/test_util/gtest_signal_stacktrace_printer.hpp> // NOLINT

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <stack>
#include <utility>

using namespace ::monad;
using namespace ::monad::mpt;
using namespace ::monad::test;

TEST_F(OnDiskMerkleTrieGTest, recursively_verify_versions)
{
    struct ExpectedSubtrieVersion
    {
        Node *root{nullptr};
        // record the calculated min max versions in traversal
        int64_t min_subtrie_version{
            std::numeric_limits<int64_t>::max()}; // include node itself
        int64_t max_children_version{0}; // exclude node
    };

    struct TraverseVerifyVersions : public TraverseMachine
    {
        std::stack<ExpectedSubtrieVersion> &records;
        bool done_erase{false};

        TraverseVerifyVersions(
            std::stack<ExpectedSubtrieVersion> &records,
            bool done_erase_ = false)
            : records(records)
            , done_erase{done_erase_}
        {
        }

        virtual bool down(unsigned char, SubtrieInfo const subtrie) override
        {
            records.push(ExpectedSubtrieVersion{
                .root = const_cast<Node *>(&subtrie.node),
                .min_subtrie_version = subtrie.node.version,
                .max_children_version = 0});
            return true;
        }

        virtual void
        up(unsigned char const branch, SubtrieInfo const subtrie) override
        {
            auto const node_record = records.top();
            auto const &node = subtrie.node;
            ASSERT_TRUE(node_record.root == &node);
            records.pop();
            if (records.empty()) { // node is root
                EXPECT_EQ(
                    node_record.min_subtrie_version,
                    calc_min_version(*const_cast<Node *>(&node)));
            }
            else {
                auto &parent_record = records.top();
                Node *const parent = parent_record.root;
                // verify version decreasing
                EXPECT_TRUE(parent->version >= node.version);

                // verify max_children_version for non leaf nodes
                if (!node.has_value()) {
                    if (done_erase) {
                        EXPECT_TRUE(
                            node.version >= node_record.max_children_version);
                    }
                    else {
                        EXPECT_EQ(
                            node.version, node_record.max_children_version);
                    }
                }
                else {
                    EXPECT_EQ(node_record.max_children_version, 0);
                }
                // verify min_subtrie_version
                EXPECT_EQ(
                    node_record.min_subtrie_version,
                    parent->subtrie_min_version(
                        parent->to_child_index(branch)));
                // update parent record
                parent_record.min_subtrie_version = std::min(
                    parent_record.min_subtrie_version,
                    node_record.min_subtrie_version);
                parent_record.max_children_version =
                    std::max(parent_record.max_children_version, node.version);
            }
        }

        virtual std::unique_ptr<TraverseMachine> clone() const override
        {
            return std::make_unique<TraverseVerifyVersions>(*this);
        }
    };

    this->sm = std::make_unique<StateMachineAlwaysMerkle>();

    // Do 100 random updates for 1000 blocks, using aux.do_update()
    // A full traversal to verify versions are correct, and nodes of all
    // versions should exists, root min_version should be 0
    constexpr uint64_t NUM_BLOCKS = 1000;
    constexpr unsigned BATCH_SIZE = 100;
    uint64_t i = 0;
    for (uint64_t block_id = 0; block_id < NUM_BLOCKS; ++block_id) {
        std::vector<byte_string> key_values;
        key_values.reserve(BATCH_SIZE);
        std::vector<Update> updates_alloc;
        updates_alloc.reserve(BATCH_SIZE);
        UpdateList updates;
        for (unsigned n = 0; n < BATCH_SIZE; ++n) {
            byte_string kv(KECCAK256_SIZE, 0);
            MONAD_ASSERT(kv.size() == KECCAK256_SIZE);
            keccak256((unsigned char const *)&i, 8, kv.data());
            key_values.emplace_back(kv);

            updates.push_front(updates_alloc.emplace_back(Update{
                .key = key_values.back(),
                .value = key_values.back(),
                .incarnation = false,
                .next = UpdateList{},
                .version = static_cast<int64_t>(block_id)}));
            i++;
        }
        this->root = this->aux.do_update(
            std::move(this->root), *this->sm, std::move(updates), block_id);
    }

    {
        std::stack<ExpectedSubtrieVersion> node_records{};
        EXPECT_EQ(calc_min_version(*this->root), 0);

        TraverseVerifyVersions traverse{node_records};
        // Must traverse in order
        preorder_traverse_blocking(
            this->aux,
            *this->root,
            traverse,
            this->aux.db_history_max_version());
        EXPECT_EQ(traverse.records.empty(), true);
    }

    // Erase half of the keys
    // A full traversal to verify versions are correct
    constexpr unsigned ERASE_BATCH_SIZE = BATCH_SIZE / 2;
    for (uint64_t new_id = 0; new_id < NUM_BLOCKS; ++new_id) {
        uint64_t block_id = new_id + NUM_BLOCKS;
        std::vector<byte_string> key_values;
        key_values.reserve(ERASE_BATCH_SIZE);
        std::vector<Update> updates_alloc;
        updates_alloc.reserve(ERASE_BATCH_SIZE);
        UpdateList updates;
        i = new_id * BATCH_SIZE;
        for (unsigned n = 0; n < ERASE_BATCH_SIZE; ++n) {
            byte_string kv(KECCAK256_SIZE, 0);
            MONAD_ASSERT(kv.size() == KECCAK256_SIZE);
            keccak256((unsigned char const *)&i, 8, kv.data());
            key_values.emplace_back(kv);

            updates.push_front(updates_alloc.emplace_back(Update{
                .key = key_values.back(),
                .value = std::nullopt,
                .incarnation = false,
                .next = UpdateList{},
                .version = static_cast<int64_t>(block_id)}));
            i++;
        }
        this->root = this->aux.do_update(
            std::move(this->root), *this->sm, std::move(updates), block_id);
    }

    {
        std::stack<ExpectedSubtrieVersion> node_records{};
        EXPECT_EQ(calc_min_version(*this->root), 0);

        TraverseVerifyVersions traverse{node_records, true};
        // Must traverse in order
        preorder_traverse_blocking(
            this->aux,
            *this->root,
            traverse,
            this->aux.db_history_max_version());
        EXPECT_EQ(traverse.records.empty(), true);
    }
}
