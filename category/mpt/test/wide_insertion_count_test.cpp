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

#include "legacy_metadata.hpp"
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

#include <atomic>
#include <bit>
#include <cstdint>
#include <cstring>
#include <filesystem>
#include <optional>
#include <utility>
#include <vector>

#include <stdlib.h>
#include <sys/types.h>
#include <unistd.h>

using namespace monad::mpt;

namespace
{
    // The first count the 20-bit field in chunk_info_t cannot hold.
    constexpr uint64_t NARROW_LIMIT = uint64_t{1} << 20;
    constexpr uint64_t HISTORY_LENGTH = 50;

    std::vector<uint64_t> list_counts(UpdateAux const &aux, bool const fast)
    {
        std::vector<uint64_t> counts;
        auto const *const m = aux.metadata_ctx().main();
        for (auto const *ci = fast ? m->fast_list_begin()
                                   : m->slow_list_begin();
             ci != nullptr;
             ci = ci->next(m)) {
            counts.push_back(m->insertion_count(ci->index(m)));
        }
        return counts;
    }

    class WideInsertionCounts : public ::testing::Test
    {
    protected:
        monad::async::storage_pool pool{
            monad::async::use_anonymous_inode_tag{}};
        monad::io::Ring ring1;
        monad::io::Ring ring2;
        monad::io::Buffers buffers{
            monad::io::make_buffers_for_segregated_read_write(
                ring1, ring2, 2, 4,
                monad::async::AsyncIO::MONAD_IO_BUFFERS_READ_SIZE,
                monad::async::AsyncIO::MONAD_IO_BUFFERS_WRITE_SIZE)};
        monad::async::AsyncIO io{pool, buffers};
        UpdateAux aux{};

        void init(uint64_t const first_count)
        {
            aux.set_initial_insertion_count_unit_testing_only(first_count);
            aux.init(io, HISTORY_LENGTH);
        }

        uint32_t append_free_chunk(UpdateAux::chunk_list const list)
        {
            auto &ctx = aux.metadata_ctx();
            uint32_t const idx = ctx.main()->free_list_end()->index(ctx.main());
            ctx.remove(idx);
            ctx.append(list, idx);
            return idx;
        }
    };
}

TEST_F(WideInsertionCounts, counts_keep_increasing_past_twenty_bits)
{
    init(NARROW_LIMIT - 2);
    uint32_t tail = 0;
    for (int i = 0; i < 3; ++i) {
        tail = append_free_chunk(UpdateAux::chunk_list::fast);
    }

    EXPECT_EQ(
        list_counts(aux, true),
        (std::vector<uint64_t>{
            NARROW_LIMIT - 2,
            NARROW_LIMIT - 1,
            NARROW_LIMIT,
            NARROW_LIMIT + 1}));
    EXPECT_EQ(aux.num_chunks(UpdateAux::chunk_list::fast), 4u);
    auto const virt = aux.physical_to_virtual(chunk_offset_t{tail, 0});
    EXPECT_EQ(virt.count, NARROW_LIMIT + 1);
    EXPECT_TRUE(virt.in_fast_list());
}

TEST_F(WideInsertionCounts, a_released_chunk_continues_the_free_list_counts)
{
    init(NARROW_LIMIT - 2);
    append_free_chunk(UpdateAux::chunk_list::fast);
    auto &ctx = aux.metadata_ctx();
    uint32_t const head = ctx.main()->fast_list.begin;
    ASSERT_NE(
        aux.physical_to_virtual(chunk_offset_t{head, 0}),
        INVALID_VIRTUAL_OFFSET);
    uint64_t const free_tail_count =
        ctx.main()->insertion_count(ctx.main()->free_list.end);

    ctx.remove(head);
    ctx.append(UpdateAux::chunk_list::free, head);

    EXPECT_EQ(
        aux.physical_to_virtual(chunk_offset_t{head, 0}),
        INVALID_VIRTUAL_OFFSET);
    auto const identity =
        ctx.main()->atomic_load_chunk_identity(head, std::memory_order_acquire);
    EXPECT_EQ(uint64_t(identity.count), free_tail_count + 1);
    EXPECT_FALSE(identity.in_fast_list || identity.in_slow_list);
    EXPECT_EQ(
        list_counts(aux, true), (std::vector<uint64_t>{NARROW_LIMIT - 1}));
}

TEST_F(WideInsertionCounts, an_append_at_the_count_limit_aborts)
{
    init(virtual_chunk_offset_t::MAX_COUNT - 1);
    ASSERT_DEATH(append_free_chunk(UpdateAux::chunk_list::fast), "MAX_COUNT");
}

namespace
{
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
            monad::async::working_temporary_directory(), "monad_wide_test_");
        std::filesystem::path path{
            monad::async::working_temporary_directory() /
            "monad_wide_test_XXXXXX"};
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
            std::filesystem::path const &path, uint64_t const first_count,
            bool const allow_migration = false)
            : pool{
                  path,
                  monad::async::storage_pool::mode::create_if_needed,
                  [&] {
                      auto flags = pool_flags();
                      flags.allow_migration = allow_migration;
                      return flags;
                  }()}
        {
            aux.set_initial_insertion_count_unit_testing_only(first_count);
            aux.init(io, HISTORY_LENGTH);
        }
    };

    class WideCountPool : public ::testing::Test
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

        ~WideCountPool() override
        {
            root.reset();
            rw.reset();
            std::filesystem::remove(path);
        }

        void open(uint64_t const first_count)
        {
            rw.emplace(path, first_count);
        }

        void reopen_at_latest(bool const allow_migration = false)
        {
            root.reset();
            rw.reset();
            rw.emplace(path, 0, allow_migration);
            auto const latest = rw->aux.metadata_ctx().db_history_max_version();
            root = load_root(latest);
            version = latest + 1;
        }

        uint64_t tail_count(UpdateAux::chunk_list const list) const
        {
            auto const *const m = rw->aux.metadata_ctx().main();
            bool const fast = list == UpdateAux::chunk_list::fast;
            auto const *const ci =
                fast ? m->fast_list_end() : m->slow_list_end();
            return ci == nullptr ? 0 : m->insertion_count(ci->index(m));
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
                kvs.emplace_back(hot_keys.back(), hot_value(version));
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

        uint64_t fast_head_count() const
        {
            auto const *const m = rw->aux.metadata_ctx().main();
            return m->insertion_count(m->fast_list.begin);
        }

        // {count, offset} of where the slow writer resumes.
        std::pair<uint64_t, uint64_t> slow_writer_position() const
        {
            auto const v = rw->aux.physical_to_virtual(
                rw->aux.metadata_ctx().get_start_of_wip_slow_offset());
            return {v.count, v.offset};
        }

        // Read off the disk, so it shows the layout the root was written in.
        bool root_written_in_current_layout(uint64_t const v)
        {
            auto const offset =
                rw->aux.metadata_ctx().get_root_offset_at_version(
                    v, timeline_id::primary);
            auto const [fd, base] =
                rw->pool.chunk(monad::async::storage_pool::seq, offset.id)
                    .read_fd();
            uint32_t word = 0;
            MONAD_ASSERT(
                ::pread(
                    fd,
                    &word,
                    sizeof(word),
                    static_cast<off_t>(base + offset.offset)) ==
                ssize_t(sizeof(word)));
            return decode_node_size_word(word).layout_version ==
                   NODE_LAYOUT_CURRENT;
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
    };
}

TEST_F(WideCountPool, compaction_and_gc_run_past_twenty_bits)
{
    open(NARROW_LIMIT - 4);
    write_static_block();
    ASSERT_TRUE(write_until([&] {
        return fast_head_count() > NARROW_LIMIT + 2;
    })) << "the fast list head never passed 2^20 + 2";
    ASSERT_NO_FATAL_FAILURE(expect_reads_at_history_ends());
    EXPECT_LE(rw->aux.num_chunks(UpdateAux::chunk_list::fast), POOL_CHUNKS / 2);
}

TEST_F(WideCountPool, read_only_db_reads_past_twenty_bits)
{
    open(NARROW_LIMIT - 4);
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
    ASSERT_LT(fast_head_count(), NARROW_LIMIT);
    ASSERT_NO_FATAL_FAILURE(expect_ro_reads());
    ASSERT_TRUE(write_until([&] { return fast_head_count() > NARROW_LIMIT; }))
        << "the fast list head never passed 2^20";
    ASSERT_NO_FATAL_FAILURE(expect_ro_reads());
}

TEST_F(WideCountPool, a_trie_written_in_legacy_formats_reads_back)
{
    open(0);
    rw->aux.write_legacy_formats_unit_testing_only(true);
    write_static_block();
    for (int i = 0; i < 5; ++i) {
        write_hot_block();
    }
    rw->aux.write_legacy_formats_unit_testing_only(false);
    for (int i = 0; i < 5; ++i) {
        write_hot_block();
    }
    uint64_t const first_hot_version = 1;
    uint64_t const last_legacy_version = 5;
    uint64_t const latest = version - 1;

    auto const expect_all = [&] {
        for (uint64_t v = 0; v <= latest; ++v) {
            auto const r = load_root(v);
            ASSERT_TRUE(r);
            EXPECT_EQ(r->value().size(), v <= last_legacy_version ? 8u : 16u);
            EXPECT_EQ(
                root_written_in_current_layout(v), v > last_legacy_version)
                << "version " << v;
        }
        ASSERT_NO_FATAL_FAILURE(expect_reads_at(first_hot_version));
        ASSERT_NO_FATAL_FAILURE(expect_reads_at(latest));
    };
    ASSERT_NO_FATAL_FAILURE(expect_all());

    rw.reset();
    open(0);
    ASSERT_NO_FATAL_FAILURE(expect_all());
}

TEST_F(
    WideCountPool, an_upgraded_legacy_pool_reads_compacts_and_frees_old_nodes)
{
    open(NARROW_LIMIT - 4);
    rw->aux.write_legacy_formats_unit_testing_only(true);
    write_static_block();
    constexpr int LEGACY_HOT_BLOCKS = 9;
    for (int i = 0; i < LEGACY_HOT_BLOCKS; ++i) {
        write_hot_block();
    }
    uint64_t const last_legacy_fast = tail_count(UpdateAux::chunk_list::fast);
    ASSERT_LT(last_legacy_fast, NARROW_LIMIT);
    uint64_t const last_legacy_version = version - 1;
    ASSERT_FALSE(root_written_in_current_layout(last_legacy_version));
    root.reset();
    rw.reset();

    {
        monad::async::storage_pool pool{
            path,
            monad::async::storage_pool::mode::open_existing,
            pool_flags()};
        monad::mpt::test::provision_monad008_pool(pool);
    }
    reopen_at_latest(/*allow_migration=*/true);
    reopen_at_latest();
    auto const slow_writer_at_upgrade = slow_writer_position();

    auto const expect_ro_reads = [&] {
        RODb const ro{ReadOnlyOnDiskDbConfig{
            .dbname_path = path, .node_lru_max_mem = 1ul << 20}};
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
    ASSERT_NO_FATAL_FAILURE(expect_reads_at_history_ends());
    ASSERT_NO_FATAL_FAILURE(expect_ro_reads());

    // Midway through the legacy versions, so later legacy versions get dropped.
    uint64_t const retained_legacy_version = last_legacy_version / 2;
    ASSERT_EQ(load_root(retained_legacy_version)->value().size(), 8u);
    root.reset();
    rw->aux.rewind_to_version(retained_legacy_version);
    ASSERT_EQ(
        rw->aux.metadata_ctx().db_history_max_version(),
        retained_legacy_version);
    ASSERT_NO_FATAL_FAILURE(expect_reads_at(retained_legacy_version));
    root = load_root(retained_legacy_version);
    version = retained_legacy_version + 1;
    write_hot_block();
    ASSERT_NO_FATAL_FAILURE(expect_reads_at(retained_legacy_version + 1));

    ASSERT_TRUE(write_until([&] {
        return fast_head_count() > last_legacy_fast &&
               tail_count(UpdateAux::chunk_list::fast) > NARROW_LIMIT;
    })) << "GC never passed the last legacy chunk, or the tail never passed "
           "2^20";
    EXPECT_GT(slow_writer_position(), slow_writer_at_upgrade)
        << "compaction never moved live nodes out of the fast list";
    ASSERT_NO_FATAL_FAILURE(expect_reads_at_history_ends());
    ASSERT_NO_FATAL_FAILURE(expect_ro_reads());
}
