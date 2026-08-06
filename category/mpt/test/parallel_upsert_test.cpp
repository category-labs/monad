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

#include <category/core/byte_string.hpp>
#include <category/core/bytes.hpp>
#include <category/core/keccak.h>
#include <category/core/keccak.hpp>
#include <category/core/small_prng.hpp>
#include <category/core/test_util/gtest_signal_stacktrace_printer.hpp> // NOLINT
#include <category/mpt/detail/timeline.hpp>
#include <category/mpt/nibbles_view.hpp>
#include <category/mpt/node.hpp>
#include <category/mpt/node_cursor.hpp>
#include <category/mpt/parallel_upsert.hpp>
#include <category/mpt/state_machine.hpp>
#include <category/mpt/trie.hpp>
#include <category/mpt/update.hpp>
#include <category/mpt/util.hpp>

#include <gtest/gtest.h>

#include <cstddef>
#include <cstdint>
#include <tuple>
#include <utility>
#include <vector>

using namespace ::monad::test;
using namespace ::monad::mpt;

namespace
{
    constexpr uint64_t VERSION = 0;

    using kv = std::pair<monad::byte_string, monad::byte_string>;

    // Key and value bytes, owned separately from the Update objects: an upsert
    // consumes its UpdateList, so every replay needs fresh Updates over the
    // same bytes.
    struct Workload
    {
        struct Entry
        {
            monad::byte_string key;
            monad::byte_string value;
            // Nested trie under the leaf, i.e. an account's storage. Nodes that
            // carry both a value and children are the only ones whose merkle
            // compute keeps state across calls, so partitioning is only race
            // free with them present.
            std::vector<kv> nested;
        };

        std::vector<Entry> entries;
    };

    // Update objects for one upsert. The nested ones are referenced by the
    // top-level list, so they must outlive it.
    struct BuiltUpdates
    {
        std::vector<std::vector<Update>> nested;
        std::vector<Update> top;
    };

    BuiltUpdates build_updates(Workload const &workload)
    {
        BuiltUpdates built;
        built.nested.resize(workload.entries.size());
        built.top.reserve(workload.entries.size());
        for (size_t n = 0; n < workload.entries.size(); ++n) {
            auto const &entry = workload.entries[n];
            auto &nested = built.nested[n];
            nested.reserve(entry.nested.size());
            UpdateList nested_list;
            for (auto const &[key, value] : entry.nested) {
                nested.push_back(
                    make_update(key, value, false, UpdateList{}, VERSION));
                nested_list.push_front(nested.back());
            }
            built.top.push_back(make_update(
                entry.key,
                entry.value,
                false,
                std::move(nested_list),
                VERSION));
        }
        return built;
    }

    monad::byte_string random_key(monad::small_prng &rand)
    {
        monad::byte_string key(sizeof(monad::bytes32_t), 0);
        for (size_t n = 0; n < key.size(); n += 4) {
            *(uint32_t *)(key.data() + n) = rand();
        }
        return key;
    }

    void force_leading_nibbles(monad::byte_string &key, unsigned const nibbles)
    {
        for (unsigned n = 0; n < nibbles; ++n) {
            unsigned const shift = (n % 2 == 0) ? 4 : 0;
            auto &byte = key[n / 2];
            byte = static_cast<unsigned char>(
                (byte & ~(0xfu << shift)) | (0x5u << shift));
        }
    }

    /*! \brief Random keys, every fourth one carrying a nested trie.

    `shared_nibbles` leading nibbles are forced identical across every key,
    which pushes the branching - and with it the partition boundary - below a
    long shared path.
    */
    Workload make_workload(
        size_t const count, unsigned const shared_nibbles, uint32_t const seed)
    {
        monad::small_prng rand{seed};
        Workload workload;
        workload.entries.reserve(count);
        for (size_t n = 0; n < count; ++n) {
            Workload::Entry entry;
            entry.key = random_key(rand);
            force_leading_nibbles(entry.key, shared_nibbles);
            entry.value = random_key(rand);
            if (n % 4 == 0) {
                for (unsigned slot = 0; slot < 8; ++slot) {
                    entry.nested.emplace_back(
                        random_key(rand), random_key(rand));
                }
            }
            workload.entries.push_back(std::move(entry));
        }
        return workload;
    }

    monad::byte_string
    compute_root_hash(StateMachine &sm, Node::SharedPtr const &root)
    {
        if (root == nullptr) {
            return empty_trie_hash;
        }
        monad::byte_string res(KECCAK256_SIZE, 0);
        auto const len = sm.get_compute().compute(res.data(), *root);
        if (len < KECCAK256_SIZE) {
            monad::keccak256(res.data(), len, res.data());
        }
        return res;
    }

    // The reference root: an in-memory trie built by the same recursion with
    // writing and partitioning both off.
    monad::byte_string serial_root_hash(Workload const &workload)
    {
        UpdateAux aux;
        StateMachineAlwaysMerkle sm;
        auto built = build_updates(workload);
        auto const root =
            upsert_vector(aux, sm, nullptr, std::move(built.top), VERSION);
        return compute_root_hash(sm, root);
    }

    struct ParallelUpsertTest
        : public OnDiskMerkleTrieGTest
        , public ::testing::WithParamInterface<std::tuple<unsigned, uint32_t>>
    {
        unsigned workers() const
        {
            return std::get<0>(GetParam());
        }

        uint32_t partition_min_updates() const
        {
            return std::get<1>(GetParam());
        }

        void upsert_workload(Workload const &workload)
        {
            ParallelUpsertContext ctx{workers(), partition_min_updates()};
            auto built = build_updates(workload);
            aux.set_parallel(&ctx);
            root = upsert_vector(
                aux, *sm, std::move(root), std::move(built.top), VERSION);
            aux.set_parallel(nullptr);
        }

        // Reads every key back from the on-disk trie. A subtrie whose child
        // offsets were patched wrongly still hashes correctly, so the root hash
        // alone does not prove the write side.
        void expect_all_readable(Workload const &workload)
        {
            for (auto const &entry : workload.entries) {
                auto const [cursor, res] = find_blocking(
                    aux, root, entry.key, VERSION, timeline_id::primary);
                ASSERT_EQ(res, find_result::success);
                ASSERT_TRUE(cursor.is_valid());
                EXPECT_EQ(cursor.node->value(), entry.value);
                for (auto const &[key, value] : entry.nested) {
                    auto const nested_key =
                        concat(NibblesView{entry.key}, NibblesView{key});
                    auto const [nested_cursor, nested_res] = find_blocking(
                        aux, root, nested_key, VERSION, timeline_id::primary);
                    ASSERT_EQ(nested_res, find_result::success);
                    ASSERT_TRUE(nested_cursor.is_valid());
                    EXPECT_EQ(nested_cursor.node->value(), value);
                }
            }
        }
    };
}

TEST_P(ParallelUpsertTest, root_matches_serial)
{
    auto const workload = make_workload(1000, 0, 42);
    upsert_workload(workload);
    EXPECT_EQ(compute_root_hash(*sm, root), serial_root_hash(workload));
    expect_all_readable(workload);
}

// The partition depth falls inside a path shared by every key, so the cut lands
// at the first child recursion below it rather than at an exact depth.
TEST_P(ParallelUpsertTest, root_matches_serial_under_shared_path)
{
    auto const workload = make_workload(1000, 8, 43);
    upsert_workload(workload);
    EXPECT_EQ(compute_root_hash(*sm, root), serial_root_hash(workload));
    expect_all_readable(workload);
}

// A second upsert descends the trie the first one wrote, so the service thread
// reads old nodes back while workers build the new subtries.
TEST_P(ParallelUpsertTest, root_matches_serial_across_two_upserts)
{
    auto const first = make_workload(500, 0, 44);
    auto const second = make_workload(500, 0, 45);
    upsert_workload(first);
    upsert_workload(second);

    Workload both;
    both.entries = first.entries;
    both.entries.insert(
        both.entries.end(), second.entries.begin(), second.entries.end());
    EXPECT_EQ(compute_root_hash(*sm, root), serial_root_hash(both));
    expect_all_readable(both);
}

INSTANTIATE_TEST_SUITE_P(
    Workers, ParallelUpsertTest,
    ::testing::Combine(
        ::testing::Values(1u, 2u, 8u),
        // 2 splits at every opportunity, so partitions nest as deep as the
        // trie allows; 1000 leaves only the top levels partitioned; 100000
        // exceeds the workload, so nothing is handed over at all.
        ::testing::Values(uint32_t{2}, uint32_t{1000}, uint32_t{100000})));
