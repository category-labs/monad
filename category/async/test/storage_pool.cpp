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

#include "gtest/gtest-death-test.h"
#include "gtest/gtest.h"

#include <category/async/config.hpp>
#include <category/async/detail/scope_polyfill.hpp>
#include <category/async/storage_pool.hpp>
#include <category/async/test/storage_pool_test_access.hpp>
#include <category/async/util.hpp>
#include <category/core/assert.h>
#include <category/core/log.hpp>
#include <category/core/test_util/gtest_signal_stacktrace_printer.hpp> // NOLINT
#include <category/core/test_util/temp_file_cleanup.hpp>

#include <array>
#include <cstddef>
#include <cstdint>
#include <cstring>
#include <filesystem>
#include <iostream>
#include <optional>
#include <stdio.h>
#include <vector>

#include <fcntl.h>
#include <stdlib.h>
#include <unistd.h>

namespace
{
    using namespace MONAD_ASYNC_NAMESPACE;

    inline void print_pool_statistics(storage_pool &pool)
    {
        auto const &device = pool.device();
        auto const capacity = device.capacity();
        std::cout << "Pool device: chunks = " << device.chunks()
                  << " capacity = " << capacity.first
                  << " used = " << capacity.second
                  << " path = " << device.current_path();
        std::cout << "\n\n    Total conventional chunks = "
                  << pool.chunks(storage_pool::cnv);
        std::cout << "\nTotal sequential write chunks = "
                  << pool.chunks(storage_pool::seq);
        std::cout << "\n   First conventional chunk ";
        {
            auto const chunk = pool.chunk(storage_pool::cnv, 0);
            std::cout << "has capacity = " << chunk.capacity()
                      << " used = " << chunk.size();
        }
        std::cout << "\n   First sequential chunk ";
        {
            auto const chunk = pool.chunk(storage_pool::seq, 0);
            std::cout << "has capacity = " << chunk.capacity()
                      << " used = " << chunk.size();
        }
        std::cout << std::endl;
    }

    inline void run_tests(storage_pool &pool)
    {
        auto chunk1 = pool.chunk(storage_pool::cnv, 0);
        auto chunk2 = pool.chunk(storage_pool::seq, 0);
        auto chunk3 = pool.chunk(
            storage_pool::seq,
            static_cast<uint32_t>(pool.chunks(storage_pool::seq) - 1));
        print_pool_statistics(pool);

        std::vector<std::byte> buffer(1024 * 1024);
        memset(buffer.data(), 0xee, buffer.size());
        std::cout << "\n\nWriting to conventional chunk ..." << std::endl;
        EXPECT_EQ(chunk1.size(), chunk1.capacity()); // always full
        auto fd = chunk1.write_fd(buffer.size());
        EXPECT_EQ(fd.second, 0);
        MONAD_ASSERT(
            -1 != ::pwrite(
                      fd.first,
                      buffer.data(),
                      buffer.size(),
                      static_cast<off_t>(fd.second)));
        EXPECT_EQ(chunk1.size(), chunk1.capacity()); // always full

        memset(buffer.data(), 0xaa, buffer.size());
        fd = chunk1.write_fd(buffer.size());
        EXPECT_EQ(fd.second, 0);
        MONAD_ASSERT(
            -1 != ::pwrite(
                      fd.first,
                      buffer.data(),
                      buffer.size(),
                      static_cast<off_t>(fd.second + buffer.size())));
        EXPECT_EQ(chunk1.size(), chunk1.capacity()); // always full
        print_pool_statistics(pool);

        memset(buffer.data(), 0x77, buffer.size());
        std::cout << "\n\nWriting to first sequential chunk ..." << std::endl;
        fd = chunk2.write_fd(buffer.size());
        EXPECT_EQ(fd.second, chunk1.capacity() * 3);
        MONAD_ASSERT(
            -1 != ::pwrite(
                      fd.first,
                      buffer.data(),
                      buffer.size(),
                      static_cast<off_t>(fd.second)));
        EXPECT_EQ(chunk2.size(), buffer.size());
        print_pool_statistics(pool);

        memset(buffer.data(), 0x55, buffer.size());
        fd = chunk2.write_fd(buffer.size());
        EXPECT_EQ(fd.second, chunk1.capacity() * 3 + buffer.size());
        MONAD_ASSERT(
            -1 != ::pwrite(
                      fd.first,
                      buffer.data(),
                      buffer.size(),
                      static_cast<off_t>(fd.second)));
        EXPECT_EQ(chunk2.size(), buffer.size() * 2);
        print_pool_statistics(pool);

        memset(buffer.data(), 0x33, buffer.size());
        std::cout << "\n\nWriting to last sequential chunk ..." << std::endl;
        fd = chunk3.write_fd(buffer.size());
        EXPECT_EQ(
            fd.second,
            chunk1.capacity() * 2 +
                chunk1.capacity() * pool.chunks(storage_pool::seq));
        MONAD_ASSERT(
            -1 != ::pwrite(
                      fd.first,
                      buffer.data(),
                      buffer.size(),
                      static_cast<off_t>(fd.second)));
        EXPECT_EQ(chunk3.size(), buffer.size());
        print_pool_statistics(pool);

        memset(buffer.data(), 0x22, buffer.size());
        fd = chunk3.write_fd(buffer.size());
        EXPECT_EQ(
            fd.second,
            chunk1.capacity() * 2 +
                chunk1.capacity() * pool.chunks(storage_pool::seq) +
                buffer.size());
        MONAD_ASSERT(
            -1 != ::pwrite(
                      fd.first,
                      buffer.data(),
                      buffer.size(),
                      static_cast<off_t>(fd.second)));
        EXPECT_EQ(chunk3.size(), buffer.size() * 2);
        print_pool_statistics(pool);

        std::vector<std::byte> buffer2(buffer.size());
        auto check = [&](auto &chunk, int a, int b) {
            auto const fd = chunk.read_fd();
            MONAD_ASSERT(
                -1 != ::pread(
                          fd.first,
                          buffer2.data(),
                          buffer2.size(),
                          static_cast<off_t>(fd.second) + 0));
            memset(buffer.data(), a, buffer.size());
            EXPECT_EQ(0, memcmp(buffer.data(), buffer2.data(), buffer.size()));
            MONAD_ASSERT(
                -1 != ::pread(
                          fd.first,
                          buffer2.data(),
                          buffer2.size(),
                          static_cast<off_t>(fd.second + buffer.size())));
            memset(buffer.data(), b, buffer.size());
            EXPECT_EQ(0, memcmp(buffer.data(), buffer2.data(), buffer.size()));
        };
        std::cout << "\n\nChecking contents of conventional chunk ..."
                  << std::endl;
        check(chunk1, 0xee, 0xaa);
        std::cout << "\n\nChecking contents of first sequential chunk ..."
                  << std::endl;
        check(chunk2, 0x77, 0x55);
        std::cout << "\n\nChecking contents of last sequential chunk ..."
                  << std::endl;
        check(chunk3, 0x33, 0x22);

        std::cout << "\n\nDestroying contents of last sequential chunk ..."
                  << std::endl;
        print_pool_statistics(pool);
        chunk3.destroy_contents();
        EXPECT_EQ(chunk1.size(), chunk1.capacity()); // always full
        EXPECT_EQ(chunk2.size(), buffer.size() * 2);
        EXPECT_EQ(chunk3.size(), 0);
        check(chunk1, 0xee, 0xaa);
        check(chunk2, 0x77, 0x55);
        check(chunk3, 0x00, 0x00);
        print_pool_statistics(pool);

        std::cout << "\n\nDestroying contents of conventional chunk ..."
                  << std::endl;
        chunk1.destroy_contents();
        EXPECT_EQ(chunk1.size(), chunk1.capacity()); // always full
        EXPECT_EQ(chunk2.size(), buffer.size() * 2);
        EXPECT_EQ(chunk3.size(), 0);
        check(chunk1, 0x00, 0x00);
        check(chunk2, 0x77, 0x55);
        check(chunk3, 0x00, 0x00);
        print_pool_statistics(pool);

        std::cout << "\n\nDestroying contents of first sequential chunk ..."
                  << std::endl;
        chunk2.destroy_contents();
        EXPECT_EQ(chunk1.size(), chunk1.capacity()); // always full
        EXPECT_EQ(chunk2.size(), 0);
        EXPECT_EQ(chunk3.size(), 0);
        check(chunk1, 0x00, 0x00);
        check(chunk2, 0x00, 0x00);
        check(chunk3, 0x00, 0x00);
        print_pool_statistics(pool);

        std::cout << "\n\nReleasing chunks ..." << std::endl;
        print_pool_statistics(pool);
    }

    TEST(StoragePool, anonymous_inode)
    {
        storage_pool pool(use_anonymous_inode_tag{});
        run_tests(pool);
    }

    TEST(StoragePool, raw_partitions)
    {
        // open_device_ is the first thing to touch the source, so a path that
        // cannot be opened aborts before any device has been modified.
        ASSERT_DEATH(
            ({
                storage_pool const pool(
                    "/dev/mapper/raid0-rawblk0", storage_pool::mode::truncate);
            }),
            "open failed");
    }

    // The config hash folds the device's identity, so a pool copied bytewise
    // onto another device is refused rather than silently adopted.
    TEST(StoragePool, config_hash_differs)
    {
        auto create_temp_file =
            [](file_offset_t length) -> std::filesystem::path {
            monad::test::remove_stale_temp_files_once(
                working_temporary_directory(), "monad_storage_pool_test_");
            std::filesystem::path ret(
                working_temporary_directory() /
                "monad_storage_pool_test_XXXXXX");
            int const fd = ::mkstemp((char *)ret.native().data());
            MONAD_ASSERT(fd != -1);
            MONAD_ASSERT(
                -1 != ::ftruncate(fd, static_cast<off_t>(length + 16384)));
            ::close(fd);
            return ret;
        };
        // copy_file does not preserve holes, so the pool is sized at the
        // smallest a pool can be, the conventional chunks plus one, to keep
        // what this writes to 64 Mb.
        static constexpr uint32_t CHUNK_CAPACITY_BITS = 24;
        static constexpr file_offset_t BLKSIZE = 1ULL << CHUNK_CAPACITY_BITS;
        storage_pool::creation_flags flags;
        flags.set_chunk_capacity(CHUNK_CAPACITY_BITS);
        auto const dev = create_temp_file(4 * BLKSIZE);
        auto const copy = create_temp_file(4 * BLKSIZE);
        auto const undevs = monad::make_scope_exit([&]() noexcept {
            std::filesystem::remove(dev);
            std::filesystem::remove(copy);
        });
        {
            storage_pool const _{
                dev, storage_pool::mode::create_if_needed, flags};
        }
        std::filesystem::copy_file(
            dev, copy, std::filesystem::copy_options::overwrite_existing);
        // A rescan sees the same foreign footer, and preview_rescan is what
        // puts a confirmation prompt in front of one: refusing only at the
        // open below would mean prompting for an operation that then refuses.
        ASSERT_DEATH(
            storage_pool::preview_rescan(
                copy,
                std::nullopt,
                storage_pool::db_metadata_budget::no_database()),
            "initialised with a configuration different to this storage pool");
        ASSERT_DEATH(
            (storage_pool{copy, storage_pool::mode::open_existing, flags}),
            "was initialised with a configuration different to this storage "
            "pool");
        storage_pool{copy, storage_pool::mode::truncate, flags};
    }

    TEST(StoragePool, config_hash_formula_is_pinned)
    {
        using monad::async::test::StoragePoolConfigHashInput;
        using monad::async::test::StoragePoolTestAccess;

        // Fixed, hardcoded inputs -- not read from a real device, whose
        // unique_hash varies by inode and filesystem -- so this test isolates
        // compute_config_hash_ itself. This value pins the on-disk format:
        // changing it means every existing pool becomes unopenable.
        StoragePoolConfigHashInput const device{
            0x1122334455667788ULL, 4091, 1u << 28};
        EXPECT_EQ(
            StoragePoolTestAccess::compute_config_hash(device), 0xcc1041d7u);
    }

    TEST(StoragePool, rescan_refuses_a_device_the_metadata_cannot_describe)
    {
        using monad::async::test::StoragePoolRescanInput;
        using monad::async::test::StoragePoolTestAccess;

        // A budget the size of MONAD008's, which the pool only does
        // arithmetic with: a 2Mb chunk capacity leaves 1Mb of database
        // metadata, which this header and 8 bytes per chunk exhaust at about
        // 65000 chunks.
        static constexpr storage_pool::db_metadata_budget budget{
            .header_bytes = 528512, .bytes_per_chunk = 8};
        static constexpr file_offset_t TWO_MB = 2 * 1024 * 1024;
        ASSERT_DEATH(
            StoragePoolTestAccess::validate_device_to_rescan(
                {.size = 70000 * TWO_MB,
                 .chunk_capacity = uint32_t(TWO_MB),
                 .num_cnv_chunks = 3},
                budget),
            "chunk capacity is too small");

        // At the 256Mb default the metadata budget is ample, so the 20 bit
        // chunk id space binds first.
        static constexpr file_offset_t CHUNK = 256 * 1024 * 1024;
        ASSERT_DEATH(
            StoragePoolTestAccess::validate_device_to_rescan(
                {.size = 1100000 * CHUNK,
                 .chunk_capacity = uint32_t(CHUNK),
                 .num_cnv_chunks = 3},
                budget),
            "20 bit chunk id space");
    }

    // Whether the device carries a pool footer at its end. The tests use this
    // to confirm a crash window was actually built before exercising resume.
    bool device_has_footer(std::filesystem::path const &source)
    {
        int const fd = ::open(source.c_str(), O_RDONLY | O_CLOEXEC);
        MONAD_ASSERT(fd != -1);
        auto const unfd =
            monad::make_scope_exit([fd]() noexcept { ::close(fd); });
        auto const size =
            static_cast<off_t>(std::filesystem::file_size(source));
        std::array<char, 4> magic{};
        return ::pread(fd, magic.data(), magic.size(), size - 4) == 4 &&
               memcmp(magic.data(), "MND0", 4) == 0;
    }

    // Fixture for the grow tests: builds a pool, writes a known amount into
    // one seq chunk so the device is not blank, and can then extend it in
    // place.
    struct growable_pool
    {
        static constexpr file_offset_t BLKSIZE = 256 * 1024 * 1024;
        static constexpr uint32_t MARKED_BYTES = 40960;

        std::filesystem::path dev;
        uint32_t marked_chunk{0};
        size_t chunks_before{0};
        // What db_metadata recorded for the device, i.e. its size as of the
        // pool open the constructor performed.
        file_offset_t recorded_size{0};

        explicit growable_pool(file_offset_t const length)
        {
            monad::test::remove_stale_temp_files_once(
                working_temporary_directory(), "monad_storage_pool_test_");
            dev = working_temporary_directory() /
                  "monad_storage_pool_test_XXXXXX";
            int const fd = ::mkstemp((char *)dev.native().data());
            MONAD_ASSERT(fd != -1);
            MONAD_ASSERT(
                -1 != ::ftruncate(fd, static_cast<off_t>(length + 16384)));
            ::close(fd);

            storage_pool pool{dev};
            chunks_before = pool.chunks(storage_pool::seq);
            marked_chunk = static_cast<uint32_t>(chunks_before - 1);
            // Chunk 0 is written too: a live pool always carries db_metadata,
            // so a device reading as entirely blank is not a state worth
            // modelling.
            for (uint32_t const id : {0u, marked_chunk}) {
                std::vector<std::byte> buffer(MARKED_BYTES, std::byte{0xa5});
                auto chunk = pool.chunk(storage_pool::seq, id);
                auto const wfd = chunk.write_fd(MARKED_BYTES);
                MONAD_ASSERT(
                    ssize_t(MARKED_BYTES) ==
                    ::pwrite(
                        wfd.first,
                        buffer.data(),
                        MARKED_BYTES,
                        static_cast<off_t>(wfd.second)));
            }
            recorded_size = size();
        }

        growable_pool(growable_pool const &) = delete;
        growable_pool &operator=(growable_pool const &) = delete;

        ~growable_pool()
        {
            std::filesystem::remove(dev);
        }

        void extend_to(file_offset_t const to)
        {
            int const fd = ::open(dev.c_str(), O_RDWR);
            MONAD_ASSERT(fd != -1);
            auto const unfd =
                monad::make_scope_exit([fd]() noexcept { ::close(fd); });
            MONAD_ASSERT(-1 != ::ftruncate(fd, static_cast<off_t>(to)));
        }

        file_offset_t size() const
        {
            return static_cast<file_offset_t>(std::filesystem::file_size(dev));
        }

        // What monad-mpt hands the pool: only the recorded size can locate the
        // metadata an extend stranded, so a grow is refused without it.
        storage_pool::creation_flags recorded_flags() const
        {
            storage_pool::creation_flags flags;
            flags.recorded_size_of_grown_device = recorded_size;
            flags.metadata_budget =
                storage_pool::db_metadata_budget::no_database();
            return flags;
        }
    };

    // The motivating case: one logical volume, extended in place. There is no
    // sibling to cross-check the recorded previous size against, so it is
    // validated against the stranded footer's own config_hash.
    TEST(StoragePool, grow_single_device_pool)
    {
        growable_pool fixture{10 * growable_pool::BLKSIZE};
        fixture.extend_to(14 * growable_pool::BLKSIZE + 16384);

        storage_pool pool{
            fixture.dev, storage_pool::mode::rescan, fixture.recorded_flags()};
        EXPECT_GT(pool.chunks(storage_pool::seq), fixture.chunks_before);
        EXPECT_FALSE(pool.device().is_freshly_initialised());
        EXPECT_EQ(
            pool.chunk(storage_pool::seq, fixture.marked_chunk).size(),
            growable_pool::MARKED_BYTES);
    }

    // The footer at the new end is the relocation's commit record, so a crash
    // before it is durable must leave the device re-runnable with its
    // bytes-used accounting intact. Reproduced by clearing that footer's
    // magic after a completed relocation: the new array is in place, the
    // commit is not, which is exactly the window. The recorded size is still
    // the pre-grow one there, since a crash this early is a crash before the
    // metadata layer ran at all.
    TEST(StoragePool, grow_interrupted_before_the_footer_reruns)
    {
        growable_pool fixture{10 * growable_pool::BLKSIZE};
        fixture.extend_to(14 * growable_pool::BLKSIZE + 16384);
        {
            storage_pool pool{
                fixture.dev,
                storage_pool::mode::rescan,
                fixture.recorded_flags()};
            ASSERT_EQ(
                pool.chunk(storage_pool::seq, fixture.marked_chunk).size(),
                growable_pool::MARKED_BYTES);
        }

        auto const size = fixture.size();
        {
            int const fd = ::open(fixture.dev.c_str(), O_RDWR);
            ASSERT_NE(fd, -1);
            auto const unfd =
                monad::make_scope_exit([fd]() noexcept { ::close(fd); });
            std::array<char, 4> const cleared{};
            ASSERT_EQ(
                ssize_t(cleared.size()),
                ::pwrite(
                    fd,
                    cleared.data(),
                    cleared.size(),
                    static_cast<off_t>(size - cleared.size())));
            ASSERT_EQ(0, ::fsync(fd));
        }
        ASSERT_FALSE(device_has_footer(fixture.dev))
            << "the crash window was not built";

        // Re-running redoes the whole operation from the stranded footer,
        // which this never touched.
        storage_pool pool{
            fixture.dev, storage_pool::mode::rescan, fixture.recorded_flags()};
        EXPECT_GT(pool.chunks(storage_pool::seq), fixture.chunks_before);
        EXPECT_EQ(
            pool.chunk(storage_pool::seq, fixture.marked_chunk).size(),
            growable_pool::MARKED_BYTES);
    }

    // A device can be extended again after a completed grow, and what the
    // second run must be given is the size the first one left it at.
    TEST(StoragePool, grow_twice_in_succession)
    {
        growable_pool fixture{10 * growable_pool::BLKSIZE};
        fixture.extend_to(12 * growable_pool::BLKSIZE + 16384);
        size_t after_first = 0;
        {
            storage_pool const pool{
                fixture.dev,
                storage_pool::mode::rescan,
                fixture.recorded_flags()};
            after_first = pool.chunks(storage_pool::seq);
        }
        ASSERT_GT(after_first, fixture.chunks_before);

        // That run was a writable open, so this is what the database now
        // records for the device.
        auto const recorded = fixture.size();
        fixture.extend_to(15 * growable_pool::BLKSIZE + 16384);
        auto flags = fixture.recorded_flags();
        flags.recorded_size_of_grown_device = recorded;
        storage_pool pool{fixture.dev, storage_pool::mode::rescan, flags};
        EXPECT_GT(pool.chunks(storage_pool::seq), after_first);
        EXPECT_EQ(
            pool.chunk(storage_pool::seq, fixture.marked_chunk).size(),
            growable_pool::MARKED_BYTES);
    }

    // The new metadata region must clear the old one, or writing it would
    // destroy the bytes-used array before the new footer is durable.
    TEST(StoragePool, grow_too_small_to_clear_the_old_metadata_is_refused)
    {
        growable_pool fixture{10 * growable_pool::BLKSIZE};
        // The region is only 64 bytes plus four per chunk, so this refusal
        // takes a growth far below anything an operator would ask for; it
        // exists to keep the crash window closed, not to reject real input.
        auto const before = fixture.size();
        fixture.extend_to(before + 64);

        ASSERT_DEATH(
            storage_pool(
                fixture.dev,
                storage_pool::mode::rescan,
                fixture.recorded_flags()),
            "would overwrite the metadata being recovered");
        // Refused before anything was written: the stranded footer is still
        // the only one on the device.
        EXPECT_FALSE(device_has_footer(fixture.dev));
    }

    // The recorded size is checked against the pool's own hash before it is
    // acted on, so a wrong one is refused rather than used. Four bytes
    // spelling MND0 turn up in trie data eventually, and this is what stops
    // one of them being taken for a footer.
    TEST(StoragePool, grow_with_a_wrong_recorded_size_is_refused)
    {
        growable_pool fixture{10 * growable_pool::BLKSIZE};
        fixture.extend_to(14 * growable_pool::BLKSIZE + 16384);

        auto flags = fixture.recorded_flags();
        flags.recorded_size_of_grown_device = fixture.recorded_size - 8192;
        ASSERT_DEATH(
            storage_pool(fixture.dev, storage_pool::mode::rescan, flags),
            "nor any at the");
        EXPECT_FALSE(device_has_footer(fixture.dev));
    }

    // Without the recorded size nothing can say where the extend left the
    // metadata, and the refusal has to say how to get one.
    TEST(StoragePool, grow_without_a_recorded_size_is_refused)
    {
        growable_pool fixture{10 * growable_pool::BLKSIZE};
        fixture.extend_to(14 * growable_pool::BLKSIZE + 16384);

        storage_pool::creation_flags flags;
        flags.metadata_budget = storage_pool::db_metadata_budget::no_database();
        ASSERT_DEATH(
            storage_pool(fixture.dev, storage_pool::mode::rescan, flags),
            "must be opened writable once before its device is extended");
        EXPECT_FALSE(device_has_footer(fixture.dev));
    }

    TEST(StoragePool, clone_content)
    {
        storage_pool pool1(use_anonymous_inode_tag{});
        storage_pool pool2(use_anonymous_inode_tag{});

        std::vector<std::byte> buffer1(1024 * 1024);
        memset(buffer1.data(), 0xee, buffer1.size());
        auto chunk1 = pool1.chunk(storage_pool::seq, 0);
        {
            auto const fd = chunk1.write_fd(buffer1.size());
            MONAD_ASSERT(
                -1 != ::pwrite(
                          fd.first,
                          buffer1.data(),
                          buffer1.size(),
                          static_cast<off_t>(fd.second)));
            EXPECT_EQ(chunk1.size(), buffer1.size());
        }
        std::vector<std::byte> buffer2(1024 * 1024);
        memset(buffer2.data(), 0xcc, buffer2.size());
        auto chunk2 = pool2.chunk(storage_pool::seq, 0);
        {
            auto const cloned = chunk1.clone_contents_into(chunk2, UINT32_MAX);
            EXPECT_EQ(cloned, buffer1.size());
            auto const fd = chunk2.read_fd();
            MONAD_ASSERT(
                -1 != ::pread(
                          fd.first,
                          buffer2.data(),
                          buffer2.size(),
                          static_cast<off_t>(fd.second)));
            EXPECT_EQ(chunk2.size(), buffer1.size());
        }
        EXPECT_EQ(0, memcmp(buffer1.data(), buffer2.data(), buffer1.size()));
    }
}
