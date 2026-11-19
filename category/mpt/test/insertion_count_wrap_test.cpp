// Copyright (C) 2025-26 Category Labs, Inc.
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

#include <category/async/config.hpp>
#include <category/async/io.hpp>
#include <category/async/storage_pool.hpp>
#include <category/async/util.hpp>
#include <category/core/assert.h>
#include <category/core/byte_string.hpp>
#include <category/core/io/buffers.hpp>
#include <category/core/io/ring.hpp>
#include <category/core/small_prng.hpp>
#include <category/core/test_util/temp_file_cleanup.hpp>
#include <category/mpt/db.hpp>
#include <category/mpt/detail/db_metadata.hpp>
#include <category/mpt/detail/timeline.hpp>
#include <category/mpt/node.hpp>
#include <category/mpt/node_cursor.hpp>
#include <category/mpt/ondisk_db_config.hpp>
#include <category/mpt/trie.hpp>
#include <category/mpt/update.hpp>
#include <category/mpt/util.hpp>

#include <gtest/gtest.h>

#include <bit>
#include <cstdint>
#include <cstring>
#include <filesystem>
#include <optional>
#include <utility>
#include <vector>

#include <stdlib.h>
#include <unistd.h>

using namespace monad::mpt;

namespace
{
    constexpr uint32_t P = INSERTION_COUNT_PERIOD;
    constexpr uint64_t HISTORY_LENGTH = 50;

    std::vector<uint32_t>
    insertion_counts(UpdateAux const &aux, bool const fast)
    {
        std::vector<uint32_t> counts;
        auto const *const m = aux.metadata_ctx().main();
        for (auto const *ci = fast ? m->fast_list_begin()
                                   : m->slow_list_begin();
             ci != nullptr;
             ci = ci->next(m)) {
            counts.push_back(uint32_t(ci->insertion_count()));
        }
        return counts;
    }
}

TEST(InsertionCountWrap, fast_list_appends_cross_the_wrap)
{
    monad::async::storage_pool pool{monad::async::use_anonymous_inode_tag{}};
    monad::io::Ring ring1;
    monad::io::Ring ring2;
    monad::io::Buffers buffers =
        monad::io::make_buffers_for_segregated_read_write(
            ring1,
            ring2,
            2,
            4,
            monad::async::AsyncIO::MONAD_IO_BUFFERS_READ_SIZE,
            monad::async::AsyncIO::MONAD_IO_BUFFERS_WRITE_SIZE);
    monad::async::AsyncIO io{pool, buffers};
    UpdateAux aux{};
    aux.set_initial_insertion_count_unit_testing_only(P - 1);
    aux.init(io, HISTORY_LENGTH);

    auto &ctx = aux.metadata_ctx();
    for (int i = 0; i < 3; ++i) {
        uint32_t const idx = ctx.main()->free_list_end()->index(ctx.main());
        ctx.remove(idx);
        ctx.append(UpdateAux::chunk_list::fast, idx);
    }

    EXPECT_EQ(
        insertion_counts(aux, true), (std::vector<uint32_t>{P - 1, P, 1, 2}));
    EXPECT_EQ(aux.num_chunks(UpdateAux::chunk_list::fast), 4u);
    auto const [list, age] = aux.chunk_list_and_age(ctx.main()->fast_list.end);
    EXPECT_EQ(list, UpdateAux::chunk_list::fast);
    EXPECT_EQ(uint32_t(age), 3u);
}

namespace
{
    constexpr uint32_t FAR_FROM_WRAP = 166'781;
    constexpr size_t POOL_CHUNKS = 16;
    constexpr size_t STATIC_KEYS = 512;
    constexpr size_t HOT_KEYS = 4;
    constexpr uint64_t MAX_BLOCKS = 20'000;

    monad::async::storage_pool::creation_flags pool_flags()
    {
        monad::async::storage_pool::creation_flags flags;
        auto const bitpos = std::countr_zero(
            monad::async::AsyncIO::MONAD_IO_BUFFERS_WRITE_SIZE);
        flags.chunk_capacity = bitpos;
        return flags;
    }

    std::filesystem::path make_pool_file()
    {
        monad::test::remove_stale_temp_files_once(
            monad::async::working_temporary_directory(), "monad_wrap_test_");
        std::filesystem::path path{
            monad::async::working_temporary_directory() /
            "monad_wrap_test_XXXXXX"};
        int const fd = ::mkstemp((char *)path.native().data());
        MONAD_ASSERT(fd != -1);
        MONAD_ASSERT(
            -1 !=
            ::ftruncate(
                fd,
                (3 + POOL_CHUNKS) *
                        monad::async::AsyncIO::MONAD_IO_BUFFERS_WRITE_SIZE +
                    24576));
        ::close(fd);
        return path;
    }

    monad::byte_string random_key(monad::small_prng &rand)
    {
        monad::byte_string key(32, 0);
        for (size_t n = 0; n < key.size(); n += 4) {
            uint32_t const v = rand();
            std::memcpy(key.data() + n, &v, 4);
        }
        return key;
    }

    monad::byte_string hot_value(uint64_t const version)
    {
        return serialize_as_big_endian<8>(version);
    }

    struct RwPool
    {
        monad::async::storage_pool pool;
        monad::io::Ring ring1{monad::io::RingConfig{2}};
        monad::io::Ring ring2{monad::io::RingConfig{4}};
        monad::io::Buffers rwbuf{
            monad::io::make_buffers_for_segregated_read_write(
                ring1, ring2, 2, 4,
                monad::async::AsyncIO::MONAD_IO_BUFFERS_READ_SIZE,
                monad::async::AsyncIO::MONAD_IO_BUFFERS_WRITE_SIZE)};
        monad::async::AsyncIO io{pool, rwbuf};
        UpdateAux aux{};

        RwPool(
            std::filesystem::path const &path, uint32_t const first_count,
            std::optional<uint64_t> const history_length = HISTORY_LENGTH)
            : pool{
                  path,
                  monad::async::storage_pool::mode::create_if_needed,
                  pool_flags()}
        {
            aux.set_initial_insertion_count_unit_testing_only(first_count);
            aux.init(io, history_length);
        }
    };

    class InsertionCountWrapPool : public ::testing::Test
    {
    protected:
        std::filesystem::path const path{make_pool_file()};
        std::optional<RwPool> rw;
        monad::test::StateMachineAlwaysMerkle sm;
        Node::SharedPtr root;
        uint64_t version{0};
        monad::small_prng rand;
        std::vector<monad::byte_string> static_keys;
        std::vector<monad::byte_string> hot_keys;

        ~InsertionCountWrapPool() override
        {
            root.reset();
            rw.reset();
            std::filesystem::remove(path);
        }

        void open(
            uint32_t const first_count,
            std::optional<uint64_t> const history_length = HISTORY_LENGTH)
        {
            rw.emplace(path, first_count, history_length);
        }

        void reopen()
        {
            root.reset();
            rw.reset();
            rw.emplace(path, 0);
            root = load_root(rw->aux.metadata_ctx().db_history_max_version());
        }

        Node::SharedPtr load_root(uint64_t const v) const
        {
            auto const &aux = rw->aux;
            return read_node_blocking(
                aux,
                aux.metadata_ctx().get_root_offset_at_version(
                    v, timeline_id::primary),
                v,
                timeline_id::primary);
        }

        void upsert(
            std::vector<std::pair<monad::byte_string, monad::byte_string>> const
                &kvs)
        {
            std::vector<Update> updates;
            updates.reserve(kvs.size());
            UpdateList ls;
            for (auto const &[k, v] : kvs) {
                updates.push_back(make_update(k, v));
                ls.push_front(updates.back());
            }
            root = rw->aux.do_update(
                std::move(root),
                sm,
                std::move(ls),
                version++,
                /*compaction=*/true,
                /*can_write_to_fast=*/true,
                /*write_root=*/true,
                timeline_id::primary);
        }

        void write_static_block()
        {
            std::vector<std::pair<monad::byte_string, monad::byte_string>> kvs;
            for (size_t i = 0; i < STATIC_KEYS; ++i) {
                static_keys.push_back(random_key(rand));
                kvs.emplace_back(static_keys.back(), static_keys.back());
            }
            for (size_t i = 0; i < HOT_KEYS; ++i) {
                hot_keys.push_back(random_key(rand));
            }
            upsert(kvs);
        }

        void write_hot_block()
        {
            std::vector<std::pair<monad::byte_string, monad::byte_string>> kvs;
            kvs.reserve(hot_keys.size());
            for (auto const &k : hot_keys) {
                kvs.emplace_back(k, hot_value(version));
            }
            upsert(kvs);
        }

        // Stores `watermark` as the root value, as an older binary could
        // have, instead of the value do_update would compute.
        void write_hot_block_with_watermark(compact_offset_pair const watermark)
        {
            monad::byte_string const value = hot_value(version);
            std::vector<Update> updates;
            updates.reserve(hot_keys.size());
            UpdateList ls;
            for (auto const &k : hot_keys) {
                updates.push_back(make_update(k, value));
                ls.push_front(updates.back());
            }
            monad::byte_string const root_value = watermark.serialize();
            Update root_update =
                make_update({}, root_value, false, std::move(ls), version);
            UpdateList root_updates;
            root_updates.push_front(root_update);
            root = monad::mpt::upsert(
                rw->aux,
                version++,
                sm,
                std::move(root),
                std::move(root_updates),
                /*write_root=*/true,
                timeline_id::primary);
        }

        uint32_t head_count(bool const fast) const
        {
            auto const *const m = rw->aux.metadata_ctx().main();
            return uint32_t((fast ? m->fast_list_begin() : m->slow_list_begin())
                                ->insertion_count());
        }

        uint32_t tail_count(bool const fast) const
        {
            auto const *const m = rw->aux.metadata_ctx().main();
            return uint32_t((fast ? m->fast_list_end() : m->slow_list_end())
                                ->insertion_count());
        }

        template <class Done>
        bool write_until(Done const &done)
        {
            for (uint64_t n = 0; n < MAX_BLOCKS && !done(); ++n) {
                write_hot_block();
            }
            return done();
        }

        void expect_reads_at(uint64_t const v)
        {
            auto const r = load_root(v);
            ASSERT_TRUE(r);
            NodeCursor const cursor{r};
            for (auto const &k : static_keys) {
                auto const [c, res] =
                    find_blocking(rw->aux, cursor, k, v, timeline_id::primary);
                ASSERT_EQ(res, find_result::success);
                EXPECT_EQ(monad::byte_string{c.node->value()}, k);
            }
            for (auto const &k : hot_keys) {
                auto const [c, res] =
                    find_blocking(rw->aux, cursor, k, v, timeline_id::primary);
                ASSERT_EQ(res, find_result::success);
                EXPECT_EQ(monad::byte_string{c.node->value()}, hot_value(v));
            }
        }

        void expect_reads_at_history_ends()
        {
            auto const &ctx = rw->aux.metadata_ctx();
            ASSERT_NO_FATAL_FAILURE(
                expect_reads_at(ctx.db_history_max_version()));
            ASSERT_NO_FATAL_FAILURE(
                expect_reads_at(ctx.db_history_min_valid_version()));
        }

        // Both components behind their list heads, as older binaries
        // persisted watermarks advanced from MIN with raw arithmetic.
        compact_offset_pair legacy_watermark() const
        {
            uint32_t const slow_head = head_count(false);
            MONAD_ASSERT(head_count(true) > 0 && slow_head > 0);
            return {
                compact_virtual_chunk_offset_t::from_count_and_truncated_offset(
                    0, 5),
                compact_virtual_chunk_offset_t::from_count_and_truncated_offset(
                    slow_head - 1, 7)};
        }
    };
}

TEST_F(InsertionCountWrapPool, compaction_frees_fast_chunks_across_the_wrap)
{
    open(P - 1);
    write_static_block();
    ASSERT_TRUE(write_until([&] { return tail_count(true) < P - 1; }))
        << "fast tail never wrapped";
    EXPECT_GE(head_count(true), P - 1);
    EXPECT_LE(rw->aux.num_chunks(UpdateAux::chunk_list::fast), POOL_CHUNKS / 2);
    ASSERT_NO_FATAL_FAILURE(
        expect_reads_at(rw->aux.metadata_ctx().db_history_max_version()));

    ASSERT_TRUE(write_until([&] { return head_count(true) < P - 1; }))
        << "fast head never crossed the wrap";
    ASSERT_NO_FATAL_FAILURE(expect_reads_at_history_ends());
    EXPECT_LE(rw->aux.num_chunks(UpdateAux::chunk_list::fast), POOL_CHUNKS / 2);
}

TEST_F(InsertionCountWrapPool, compaction_frees_chunks_far_from_the_wrap)
{
    open(FAR_FROM_WRAP);
    write_static_block();
    ASSERT_TRUE(
        write_until([&] { return head_count(true) >= FAR_FROM_WRAP + 2; }));
    ASSERT_NO_FATAL_FAILURE(expect_reads_at_history_ends());
    EXPECT_LE(rw->aux.num_chunks(UpdateAux::chunk_list::fast), POOL_CHUNKS / 2);
}

TEST_F(InsertionCountWrapPool, slow_list_tail_crosses_the_wrap)
{
    open(P - 1);
    rw->aux.alternate_slow_fast_node_writer_unit_testing_only(true);
    write_static_block();
    ASSERT_TRUE(write_until([&] { return tail_count(false) < P - 1; }))
        << "slow tail never wrapped";
    ASSERT_NO_FATAL_FAILURE(expect_reads_at_history_ends());
}

TEST_F(InsertionCountWrapPool, reopens_while_the_wrap_is_in_the_list)
{
    open(P - 1);
    write_static_block();
    ASSERT_TRUE(write_until([&] { return tail_count(true) < P - 1; }));
    ASSERT_GE(head_count(true), P - 1);
    reopen();
    ASSERT_NO_FATAL_FAILURE(expect_reads_at_history_ends());
    ASSERT_TRUE(write_until([&] { return head_count(true) < P - 1; }));
    reopen();
    ASSERT_NO_FATAL_FAILURE(expect_reads_at_history_ends());
}

TEST_F(InsertionCountWrapPool, rewinds_to_a_version_before_the_wrap)
{
    open(P - 1);
    write_static_block();
    auto const root_count = [&](uint64_t const v) {
        auto const &ctx = rw->aux.metadata_ctx();
        auto const off =
            ctx.get_root_offset_at_version(v, timeline_id::primary);
        return uint32_t(ctx.main()->at(off.id)->insertion_count());
    };
    ASSERT_TRUE(write_until([&] { return root_count(version - 1) < P - 1; }));
    uint64_t const target = version - 2;
    ASSERT_GE(root_count(target), P - 1);
    for (int i = 0; i < 5; ++i) {
        write_hot_block();
    }

    rw->aux.rewind_to_version(target);
    root = load_root(target);
    version = target + 1;
    EXPECT_EQ(rw->aux.metadata_ctx().db_history_max_version(), target);
    EXPECT_GE(tail_count(true), P - 1);
    ASSERT_NO_FATAL_FAILURE(expect_reads_at(target));

    ASSERT_TRUE(write_until([&] { return tail_count(true) < P - 1; }));
    ASSERT_NO_FATAL_FAILURE(
        expect_reads_at(rw->aux.metadata_ctx().db_history_max_version()));
}

TEST_F(InsertionCountWrapPool, a_min_watermark_pins_gc_after_the_wrap)
{
    open(P - 1);
    write_static_block();
    ASSERT_TRUE(write_until([&] { return head_count(true) < P - 1; }));

    rw->aux.activate_secondary_timeline();
    {
        auto const value = hot_value(0);
        Update update = make_update(hot_keys[0], value);
        UpdateList ls;
        ls.push_front(update);
        auto const secondary_root = rw->aux.do_update(
            nullptr,
            sm,
            std::move(ls),
            version - 1,
            /*compaction=*/false,
            /*can_write_to_fast=*/true,
            /*write_root=*/true,
            timeline_id::secondary);
        ASSERT_TRUE(secondary_root);
        EXPECT_EQ(
            compact_offset_pair::deserialize(secondary_root->value()),
            (compact_offset_pair{
                MIN_COMPACT_VIRTUAL_OFFSET, MIN_COMPACT_VIRTUAL_OFFSET}));
    }
    uint32_t const pinned_head = head_count(true);
    uint32_t const fast_chunks =
        rw->aux.num_chunks(UpdateAux::chunk_list::fast);
    ASSERT_TRUE(write_until([&] {
        return rw->aux.num_chunks(UpdateAux::chunk_list::fast) >=
               fast_chunks + 2;
    }));
    EXPECT_EQ(head_count(true), pinned_head);

    rw->aux.deactivate_secondary_timeline();
    ASSERT_TRUE(write_until([&] { return head_count(true) != pinned_head; }));
    ASSERT_NO_FATAL_FAILURE(
        expect_reads_at(rw->aux.metadata_ctx().db_history_max_version()));
}

TEST_F(InsertionCountWrapPool, read_only_db_reads_across_the_wrap)
{
    open(P - 1);
    write_static_block();
    write_hot_block();
    RODb ro{ReadOnlyOnDiskDbConfig{
        .dbname_path = path, .node_lru_max_mem = 1ul << 20}};
    auto const expect_ro_reads = [&] {
        uint64_t const v = ro.get_latest_version();
        for (auto const &k : static_keys) {
            auto const res = ro.find(k, v);
            ASSERT_TRUE(res.has_value());
            EXPECT_EQ(monad::byte_string{res.value().node->value()}, k);
        }
        for (auto const &k : hot_keys) {
            auto const res = ro.find(k, v);
            ASSERT_TRUE(res.has_value());
            EXPECT_EQ(
                monad::byte_string{res.value().node->value()}, hot_value(v));
        }
    };
    ASSERT_NO_FATAL_FAILURE(expect_ro_reads());
    ASSERT_TRUE(write_until([&] { return tail_count(true) < P - 1; }));
    ASSERT_NO_FATAL_FAILURE(expect_ro_reads());
    ASSERT_TRUE(write_until([&] { return head_count(true) < P - 1; }));
    ASSERT_NO_FATAL_FAILURE(expect_ro_reads());
}

TEST_F(InsertionCountWrapPool, a_watermark_below_the_list_heads_pins_gc_once)
{
    open(FAR_FROM_WRAP);
    write_static_block();
    ASSERT_TRUE(write_until([&] { return head_count(true) != FAR_FROM_WRAP; }));

    uint64_t const legacy_version = version;
    write_hot_block_with_watermark(legacy_watermark());
    while (version < legacy_version + HISTORY_LENGTH - 1) {
        write_hot_block();
    }
    uint32_t const pinned_head = head_count(true);
    write_hot_block();
    ASSERT_EQ(
        rw->aux.metadata_ctx().db_history_min_valid_version(), legacy_version);
    EXPECT_EQ(head_count(true), pinned_head);

    ASSERT_TRUE(write_until([&] { return head_count(true) != pinned_head; }));
    ASSERT_NO_FATAL_FAILURE(expect_reads_at_history_ends());
}

TEST_F(InsertionCountWrapPool, a_watermark_past_the_list_tail_aborts)
{
    open(FAR_FROM_WRAP);
    write_static_block();
    write_hot_block();
    write_hot_block_with_watermark(
        {compact_virtual_chunk_offset_t::from_count_and_truncated_offset(
             tail_count(true) + 8, 0),
         MIN_COMPACT_VIRTUAL_OFFSET});
    ASSERT_DEATH(write_hot_block(), "past its list's tail");
}

TEST_F(InsertionCountWrapPool, a_retained_legacy_watermark_stops_the_writer)
{
    testing::FLAGS_gtest_death_test_style = "threadsafe";
    open(P - 1);
    write_static_block();
    write_hot_block_with_watermark(legacy_watermark());
    reopen();
    ASSERT_DEATH(write_hot_block(), "an older binary wrote");
}

TEST_F(InsertionCountWrapPool, a_prev_root_into_a_released_chunk_aborts)
{
    open(FAR_FROM_WRAP);
    write_static_block();
    write_hot_block();
    Node::SharedPtr const released_root = root;
    ASSERT_TRUE(write_until([&] { return head_count(true) != FAR_FROM_WRAP; }));
    root = released_root;
    ASSERT_DEATH(
        write_hot_block(), "Detected referenced offsets in released chunks");
}

TEST_F(InsertionCountWrapPool, min_offsets_into_a_released_chunk_abort)
{
    open(FAR_FROM_WRAP);
    write_static_block();
    write_hot_block();
    Node::SharedPtr const released_root = root;
    ASSERT_TRUE(write_until([&] { return head_count(true) != FAR_FROM_WRAP; }));
    ASSERT_DEATH(
        calc_min_offsets(rw->aux, *released_root),
        "Detected referenced offsets in released chunks");
}

TEST_F(InsertionCountWrapPool, dynamic_history_trims_and_frees_across_the_wrap)
{
    constexpr size_t hot_key_count = 16;
    open(P - 1, std::nullopt);
    write_static_block();
    while (hot_keys.size() < hot_key_count) {
        hot_keys.push_back(random_key(rand));
    }
    auto const &ctx = rw->aux.metadata_ctx();
    uint64_t const initial_history_length = ctx.version_history_length();

    // With the fast list at {P - 1, P}, a count-0 watermark ranks inside it.
    ASSERT_TRUE(write_until([&] { return tail_count(true) == P; }));
    write_hot_block_with_watermark(legacy_watermark());

    ASSERT_TRUE(write_until([&] { return head_count(true) < P - 1; }))
        << "fast head never crossed the wrap";
    EXPECT_LT(ctx.version_history_length(), initial_history_length);
    EXPECT_LE(rw->aux.disk_usage(), 0.8);
    ASSERT_NO_FATAL_FAILURE(expect_reads_at_history_ends());
}
