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

#include <category/async/config.hpp>
#include <category/async/util.hpp>
#include <category/core/test_util/gtest_signal_stacktrace_printer.hpp> // NOLINT
#include <category/mpt/config.hpp>
#include <category/mpt/db_stats_shm.hpp>
#include <category/mpt/detail/collected_stats.hpp>

#include <gtest/gtest.h>

#include <atomic>
#include <cstdint>
#include <cstring>
#include <filesystem>
#include <fstream>
#include <ios>
#include <string>
#include <thread>
#include <vector>

#include <fcntl.h>
#include <sys/mman.h>
#include <unistd.h>

using namespace MONAD_MPT_NAMESPACE;

namespace
{
    detail::TrieUpdateCollectedStats uniform_stats(uint64_t const n)
    {
        return {
            .nodes_created_or_updated = n,
            .nreads_compaction = n,
            .nreads_before_compact_offset = {n, n},
            .nreads_after_compact_offset = {n, n},
            .bytes_read_before_compact_offset = {n, n},
            .bytes_read_after_compact_offset = {n, n},
            .compacted_nodes_in_fast = n,
            .compacted_nodes_in_slow = n,
            .nodes_copied_fast_to_fast_for_fast = n,
            .nodes_copied_fast_to_fast_for_slow = n,
            .nodes_copied_slow_to_fast_for_slow = n,
            .compacted_bytes_in_fast = n,
            .compacted_bytes_in_slow = n,
            .bytes_copied_slow_to_fast_for_slow = n,
            .nodes_updated_expire = n,
            .nreads_expire = n};
    }

    bool is_uniform(detail::TrieUpdateCollectedStats const &s)
    {
        uint64_t fields[sizeof(s) / sizeof(uint64_t)];
        std::memcpy(fields, &s, sizeof(s));
        for (auto const f : fields) {
            if (f != fields[0]) {
                return false;
            }
        }
        return true;
    }

    // Direct access to the mapping so tests can forge header states a
    // well-behaved publisher never produces.
    class RawMapping
    {
        int fd_{-1};
        detail::db_stats_shm *shm_{nullptr};

    public:
        explicit RawMapping(std::filesystem::path const &path)
        {
            fd_ = ::open(path.c_str(), O_RDWR);
            EXPECT_NE(fd_, -1) << "cannot open " << path;
            void *const p = ::mmap(
                nullptr,
                sizeof(detail::db_stats_shm),
                PROT_READ | PROT_WRITE,
                MAP_SHARED,
                fd_,
                0);
            EXPECT_NE(p, MAP_FAILED);
            shm_ = static_cast<detail::db_stats_shm *>(p);
        }

        ~RawMapping()
        {
            if (shm_ != nullptr) {
                ::munmap(shm_, sizeof(detail::db_stats_shm));
            }
            if (fd_ != -1) {
                ::close(fd_);
            }
        }

        RawMapping(RawMapping const &) = delete;
        RawMapping &operator=(RawMapping const &) = delete;

        detail::db_stats_shm *operator->() const noexcept
        {
            return shm_;
        }
    };

    void write_file(
        std::filesystem::path const &path, void const *const data,
        size_t const size)
    {
        std::ofstream out{path, std::ios::binary};
        out.write(
            static_cast<char const *>(data),
            static_cast<std::streamsize>(size));
    }

    struct DbStatsShmTest : public ::testing::Test
    {
        std::filesystem::path path;

        void SetUp() override
        {
            path = MONAD_ASYNC_NAMESPACE::working_temporary_directory() /
                   ("monad_db_stats_" + std::to_string(::getpid()) + "_" +
                    ::testing::UnitTest::GetInstance()
                        ->current_test_info()
                        ->name());
            std::filesystem::remove(path);
        }

        void TearDown() override
        {
            std::filesystem::remove(path);
        }
    };
}

TEST_F(DbStatsShmTest, published_stats_round_trip)
{
    auto publisher = DbStatsPublisher::create(path);
    ASSERT_TRUE(publisher.has_value());

    detail::TrieUpdateCollectedStats stats{};
    stats.nodes_created_or_updated = 42;
    stats.compacted_bytes_in_slow = 1UL << 20;
    stats.nreads_expire = 7;
    publisher->publish_update_stats(stats);

    auto const reader = DbStatsReader::open(path);
    ASSERT_TRUE(reader.has_value());
    auto const read = reader->read_update_stats();
    ASSERT_TRUE(read.has_value());
    EXPECT_EQ(read->nodes_created_or_updated, 42u);
    EXPECT_EQ(read->compacted_bytes_in_slow, 1UL << 20);
    EXPECT_EQ(read->nreads_expire, 7u);
    EXPECT_EQ(read->nreads_compaction, 0u);
}

TEST_F(DbStatsShmTest, reader_sees_each_successive_publish)
{
    auto publisher = DbStatsPublisher::create(path);
    ASSERT_TRUE(publisher.has_value());
    auto const reader = DbStatsReader::open(path);
    ASSERT_TRUE(reader.has_value());

    for (uint64_t n = 1; n <= 4; ++n) {
        publisher->publish_update_stats(uniform_stats(n));
        auto const read = reader->read_update_stats();
        ASSERT_TRUE(read.has_value());
        EXPECT_EQ(read->nodes_created_or_updated, n);
        EXPECT_EQ(read->nreads_expire, n);
    }
}

TEST_F(DbStatsShmTest, create_takes_over_a_sidecar_a_writer_died_holding)
{
    {
        auto publisher = DbStatsPublisher::create(path);
        ASSERT_TRUE(publisher.has_value());
        publisher->publish_update_stats(uniform_stats(99));
        RawMapping const raw{path};
        // A writer killed between the two halves of a publish leaves the
        // sequence odd, which is a held lock to every reader.
        std::atomic_ref<uint32_t>{raw->seq}.store(7, std::memory_order_release);
    }

    auto const publisher = DbStatsPublisher::create(path);
    ASSERT_TRUE(publisher.has_value());

    auto const reader = DbStatsReader::open(path);
    ASSERT_TRUE(reader.has_value());
    auto const read = reader->read_update_stats();
    ASSERT_TRUE(read.has_value()) << "takeover left the seqlock held";
    EXPECT_EQ(read->nodes_created_or_updated, 0u);
}

TEST_F(DbStatsShmTest, create_resets_an_existing_sidecar_without_shrinking_it)
{
    auto publisher = DbStatsPublisher::create(path);
    ASSERT_TRUE(publisher.has_value());
    publisher->publish_update_stats(uniform_stats(99));
    // A writer carrying sections this build does not know leaves a longer file.
    std::filesystem::resize_file(path, sizeof(detail::db_stats_shm) + 4096);

    // Mapped before the takeover: shrinking the file would drop this reader's
    // pages and fault it on the next read.
    auto const reader = DbStatsReader::open(path);
    ASSERT_TRUE(reader.has_value());
    publisher.reset();

    auto const successor = DbStatsPublisher::create(path);
    ASSERT_TRUE(successor.has_value());
    EXPECT_EQ(
        std::filesystem::file_size(path), sizeof(detail::db_stats_shm) + 4096);

    auto const read = reader->read_update_stats();
    ASSERT_TRUE(read.has_value());
    EXPECT_EQ(read->nodes_created_or_updated, 0u);
}

TEST_F(DbStatsShmTest, create_refuses_a_file_that_is_not_a_sidecar)
{
    std::vector<char> const other_file(4096, '\xab');
    write_file(path, other_file.data(), other_file.size());

    EXPECT_FALSE(DbStatsPublisher::create(path).has_value());

    // The load-bearing assertion: a mistyped path costs the operator their
    // metrics, never the file they named.
    std::vector<char> after(other_file.size(), '\0');
    std::ifstream in{path, std::ios::binary};
    in.read(after.data(), static_cast<std::streamsize>(after.size()));
    EXPECT_EQ(after, other_file);
    EXPECT_EQ(std::filesystem::file_size(path), other_file.size());
}

TEST_F(DbStatsShmTest, create_refuses_a_second_publisher_on_one_path)
{
    auto const first = DbStatsPublisher::create(path);
    ASSERT_TRUE(first.has_value());

    // Two publishers would interleave their seqlock updates and hand readers
    // snapshots mixing both writers' totals.
    EXPECT_FALSE(DbStatsPublisher::create(path).has_value());
}

TEST_F(DbStatsShmTest, create_publishes_again_after_the_previous_writer_exits)
{
    {
        auto const first = DbStatsPublisher::create(path);
        ASSERT_TRUE(first.has_value());
    }

    auto publisher = DbStatsPublisher::create(path);
    ASSERT_TRUE(publisher.has_value()) << "the lock outlived its publisher";
    publisher->publish_update_stats(uniform_stats(5));

    auto const reader = DbStatsReader::open(path);
    ASSERT_TRUE(reader.has_value());
    EXPECT_EQ(reader->read_update_stats()->nodes_created_or_updated, 5u);
}

TEST_F(DbStatsShmTest, open_fails_when_the_file_is_absent)
{
    EXPECT_FALSE(DbStatsReader::open(path).has_value());
}

TEST_F(DbStatsShmTest, open_fails_on_a_file_that_is_not_a_sidecar)
{
    std::vector<char> const junk(sizeof(detail::db_stats_shm), '\xff');
    write_file(path, junk.data(), junk.size());

    EXPECT_FALSE(DbStatsReader::open(path).has_value());
}

TEST_F(DbStatsShmTest, open_fails_on_a_file_too_small_for_a_header)
{
    write_file(path, "short", 5);

    EXPECT_FALSE(DbStatsReader::open(path).has_value());
}

TEST_F(DbStatsShmTest, open_accepts_a_writer_that_appended_sections)
{
    auto publisher = DbStatsPublisher::create(path);
    ASSERT_TRUE(publisher.has_value());
    publisher->publish_update_stats(uniform_stats(3));

    // Appending sections grows payload_size and leaves the layout version
    // alone, so the sections this build knows keep their offsets.
    RawMapping const raw{path};
    raw->payload_size += 64;

    auto const reader = DbStatsReader::open(path);
    ASSERT_TRUE(reader.has_value());
    auto const read = reader->read_update_stats();
    ASSERT_TRUE(read.has_value());
    EXPECT_EQ(read->nodes_created_or_updated, 3u);
}

TEST_F(DbStatsShmTest, open_fails_on_a_different_layout_version)
{
    auto const publisher = DbStatsPublisher::create(path);
    ASSERT_TRUE(publisher.has_value());

    RawMapping const raw{path};
    raw->format_version = detail::db_stats_shm::FORMAT_VERSION + 1;

    EXPECT_FALSE(DbStatsReader::open(path).has_value());
}

TEST_F(DbStatsShmTest, a_writer_predating_the_section_reads_back_as_absent)
{
    // A header-only file, as a writer with no sections at all would leave it.
    detail::db_stats_shm header{};
    header.magic = detail::db_stats_shm::MAGIC;
    header.format_version = detail::db_stats_shm::FORMAT_VERSION;
    header.payload_size = 0;
    header.seq = 2;
    write_file(path, &header, detail::db_stats_shm::HEADER_SIZE);
    ASSERT_EQ(
        std::filesystem::file_size(path), detail::db_stats_shm::HEADER_SIZE);

    auto const reader = DbStatsReader::open(path);
    ASSERT_TRUE(reader.has_value()) << "a shorter writer must still open";
    EXPECT_FALSE(reader->read_update_stats().has_value());
}

TEST_F(DbStatsShmTest, read_fails_while_a_publish_is_in_flight)
{
    auto publisher = DbStatsPublisher::create(path);
    ASSERT_TRUE(publisher.has_value());
    publisher->publish_update_stats(uniform_stats(5));

    auto const reader = DbStatsReader::open(path);
    ASSERT_TRUE(reader.has_value());
    ASSERT_TRUE(reader->read_update_stats().has_value());

    RawMapping const raw{path};
    std::atomic_ref<uint32_t>{raw->seq}.store(1, std::memory_order_release);

    EXPECT_FALSE(reader->read_update_stats().has_value());
}

TEST_F(DbStatsShmTest, concurrent_reads_never_observe_a_torn_publish)
{
#if MONAD_CONTEXT_HAVE_TSAN
    return; // the seqlock payload copy is a deliberate data race
#endif
    static constexpr uint64_t PUBLISHES = 20000;

    auto publisher = DbStatsPublisher::create(path);
    ASSERT_TRUE(publisher.has_value());
    publisher->publish_update_stats(uniform_stats(1));
    auto const reader = DbStatsReader::open(path);
    ASSERT_TRUE(reader.has_value());

    std::atomic<bool> done{false};
    std::thread writer{[&] {
        for (uint64_t n = 1; n <= PUBLISHES; ++n) {
            publisher->publish_update_stats(uniform_stats(n));
        }
        done.store(true, std::memory_order_release);
    }};

    uint64_t reads = 0;
    bool torn = false;
    while (!done.load(std::memory_order_acquire) && !torn) {
        if (auto const read = reader->read_update_stats(); read.has_value()) {
            torn = !is_uniform(*read);
            ++reads;
        }
    }
    writer.join();

    EXPECT_FALSE(torn) << "torn publish observed after " << reads << " reads";
    EXPECT_GT(reads, 0u);
}
