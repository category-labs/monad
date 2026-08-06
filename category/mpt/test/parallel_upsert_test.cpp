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

#include <category/async/config.hpp>
#include <category/async/io.hpp>
#include <category/async/storage_pool.hpp>
#include <category/core/byte_string.hpp>
#include <category/core/bytes.hpp>
#include <category/core/io/buffers.hpp>
#include <category/core/io/ring.hpp>
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

#include <bit>
#include <cstddef>
#include <cstdint>
#include <memory>
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

    // Reads every key back from the on-disk trie. A subtrie whose child
    // offsets were patched wrongly still hashes correctly, so the root hash
    // alone does not prove the write side.
    void expect_all_readable(
        UpdateAux &aux, Node::SharedPtr const &root, Workload const &workload)
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

        /* Small enough that every writer crosses several extents and their
        reservations interleave; a production sized extent would leave every
        boundary path unexecuted at test scale. Zero keeps the production
        default, where an extent holds many nodes and none of them crosses one.
        */
        size_t extent_bytes{4096};
        size_t worker_partitions{0};
        size_t nodes_written_by_workers{0};

        void upsert_workload(Workload const &workload)
        {
            ParallelUpsertContext ctx{workers(), partition_min_updates()};
            if (extent_bytes != 0) {
                ctx.set_extent_bytes_unit_testing_only(extent_bytes);
            }
            auto built = build_updates(workload);
            aux.set_parallel(&ctx);
            root = upsert_vector(
                aux, *sm, std::move(root), std::move(built.top), VERSION);
            aux.set_parallel(nullptr);
            worker_partitions += ctx.partitions_built_by_workers();
            nodes_written_by_workers += ctx.appended_nodes();
        }

        void expect_all_readable(Workload const &workload)
        {
            ::expect_all_readable(aux, root, workload);
        }
    };
}

// The one case left at the production extent size, so the configuration the
// restore actually runs is covered here and not only by DbBinarySnapshot.
TEST_P(ParallelUpsertTest, root_matches_serial)
{
    extent_bytes = 0;
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

/* A worker serializes and writes the nodes it builds itself. A partition can
also run on the service thread, which keeps using the triedb write path, so the
count is compared against how many partitions ran on a pool thread rather than
against zero. */
TEST_P(ParallelUpsertTest, workers_write_their_own_nodes)
{
    auto const workload = make_workload(1000, 0, 46);
    upsert_workload(workload);
    EXPECT_EQ(compute_root_hash(*sm, root), serial_root_hash(workload));
    expect_all_readable(workload);
    EXPECT_EQ(worker_partitions > 0, nodes_written_by_workers > 0);
}

// An extent of one disk page is smaller than a branch node, which sends those
// nodes down the bespoke-reservation path and leaves the leaves on the buffered
// one.
TEST_P(ParallelUpsertTest, extents_smaller_than_some_nodes)
{
    extent_bytes = monad::async::DISK_PAGE_SIZE;
    auto const workload = make_workload(500, 0, 47);
    upsert_workload(workload);
    EXPECT_EQ(compute_root_hash(*sm, root), serial_root_hash(workload));
    expect_all_readable(workload);
}

INSTANTIATE_TEST_SUITE_P(
    Workers, ParallelUpsertTest,
    ::testing::Combine(
        ::testing::Values(1u, 2u, 8u),
        // 2 splits at every opportunity, so partitions nest as deep as the
        // trie allows; 1000 leaves only the top levels partitioned; 100000
        // exceeds the workload, so nothing is handed over at all.
        ::testing::Values(uint32_t{2}, uint32_t{1000}, uint32_t{100000})));

namespace
{
    /* A sequential chunk this size equals one AsyncIO write buffer, the
    smallest storage_pool grants (io.cpp asserts chunk.capacity() >=
    MONAD_IO_BUFFERS_WRITE_SIZE). reset_node_writers's own startup reservation
    therefore already spans the whole first chunk before any node is written,
    so the first worker to need an extent finds none of it free and forces the
    grant path -- the free-list pop plus metadata_ctx().append that keeps
    physical_to_virtual from returning INVALID_VIRTUAL_OFFSET for the new
    chunk -- on a modest workload, while other workers are concurrently
    building their own subtries. */
    struct SmallChunkTrieGTest : public ::testing::Test
    {
        monad::async::storage_pool pool{
            monad::async::use_anonymous_inode_tag{}, [] {
                monad::async::storage_pool::creation_flags flags;
                flags.set_chunk_capacity(static_cast<uint32_t>(std::countr_zero(
                    monad::async::AsyncIO::MONAD_IO_BUFFERS_WRITE_SIZE)));
                return flags;
            }()};
        monad::io::Ring ring1{monad::io::RingConfig{2}};
        monad::io::Ring ring2{monad::io::RingConfig{4}};
        monad::io::Buffers rwbuf{
            monad::io::make_buffers_for_segregated_read_write(
                ring1, ring2, 2, 4,
                monad::async::AsyncIO::MONAD_IO_BUFFERS_READ_SIZE,
                monad::async::AsyncIO::MONAD_IO_BUFFERS_WRITE_SIZE)};
        monad::async::AsyncIO io{pool, rwbuf};
        UpdateAux aux{io, MPT_TEST_HISTORY_LENGTH};
        std::unique_ptr<StateMachine> sm{
            std::make_unique<StateMachineAlwaysMerkle>()};
        Node::SharedPtr root;
    };
}

/* The chunk grant runs under the same lock as every worker's extent
reservation, so a partition that never reaches a worker thread would leave
this vacuous; partitions_built_by_workers() pins that a worker, not just the
service thread, forced the crossing. */
TEST_F(SmallChunkTrieGTest, root_matches_serial_across_a_chunk_grant)
{
    constexpr unsigned WORKERS = 4;
    constexpr uint32_t PARTITION_MIN_UPDATES = 2;

    auto const workload = make_workload(1000, 0, 50);
    auto const fast_chunks_before = aux.num_chunks(UpdateAux::chunk_list::fast);

    ParallelUpsertContext ctx{WORKERS, PARTITION_MIN_UPDATES};
    auto built = build_updates(workload);
    aux.set_parallel(&ctx);
    root =
        upsert_vector(aux, *sm, std::move(root), std::move(built.top), VERSION);
    aux.set_parallel(nullptr);

    // A failure here means worker scheduling starved this run, not that the
    // grant path is broken -- rerun before suspecting a correctness bug.
    ASSERT_GT(ctx.partitions_built_by_workers(), 0u)
        << "no partition ran on a worker thread this run";
    // Ordered ahead of the chunk-count check on purpose: only because this
    // assertion already ruled out "the service thread did everything" does a
    // passing chunk-count check below prove a worker forced the crossing.
    // Reordering the two, or downgrading this one to EXPECT_GT, would let the
    // test keep passing while proving nothing about the worker grant path.
    EXPECT_GT(aux.num_chunks(UpdateAux::chunk_list::fast), fast_chunks_before);

    EXPECT_EQ(compute_root_hash(*sm, root), serial_root_hash(workload));
    expect_all_readable(aux, root, workload);
}
