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
#include <cmath>
#include <cstddef>
#include <cstdint>
#include <cstdio>
#include <cstring>
#include <filesystem>
#include <iostream>
#include <stdio.h>
#include <utility>
#include <vector>

#include <fcntl.h>
#include <stdlib.h>
#include <unistd.h>

namespace
{
    using namespace MONAD_ASYNC_NAMESPACE;

    inline void print_pool_statistics(storage_pool &pool)
    {
        std::cout << "Pool has " << pool.devices().size() << " devices:";
        for (size_t n = 0; n < pool.devices().size(); n++) {
            auto const &device = pool.devices()[n];
            auto const capacity = device.capacity();
            std::cout << "\n   " << (n + 1) << ". chunks = " << device.chunks()
                      << " capacity = " << capacity.first
                      << " used = " << capacity.second
                      << " path = " << device.current_path();
        }
        std::cout << "\n\n    Total conventional chunks = "
                  << pool.chunks(storage_pool::cnv);
        std::cout << "\nTotal sequential write chunks = "
                  << pool.chunks(storage_pool::seq);
        std::cout << "\n   First conventional chunk ";
        {
            auto const &chunk = pool.chunk(storage_pool::cnv, 0);
            std::cout << "has capacity = " << chunk.capacity()
                      << " used = " << chunk.size();
        }
        std::cout << "\n   First sequential chunk ";
        {
            auto const &chunk = pool.chunk(storage_pool::seq, 0);
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
            chunk1.capacity() * 2 + chunk1.capacity() *
                                        pool.chunks(storage_pool::seq) /
                                        pool.devices().size());
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
                chunk1.capacity() * pool.chunks(storage_pool::seq) /
                    pool.devices().size() +
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
        // The duplicate-source pass is the first thing to open each source, so
        // it is what reports a path that cannot be opened -- naming it, and
        // before any device has been touched.
        ASSERT_DEATH(
            ({
                std::filesystem::path const devs[] = {
                    "/dev/mapper/raid0-rawblk0", "/dev/mapper/raid0-rawblk1"};
                storage_pool const pool(devs, storage_pool::mode::truncate);
            }),
            "open of /dev/mapper/raid0-rawblk0 failed");
    }

    TEST(StoragePool, device_interleaving)
    {
        std::array<std::vector<size_t>, 3> gaps;
        auto do_test = [&](bool enable_interleaving) {
            gaps[0].clear();
            gaps[1].clear();
            gaps[2].clear();
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
            static constexpr file_offset_t BLKSIZE = 256 * 1024 * 1024;
            std::filesystem::path devs[] = {
                create_temp_file(22 * BLKSIZE),
                create_temp_file(12 * BLKSIZE),
                create_temp_file(7 * BLKSIZE)};
            auto const undevs = monad::make_scope_exit([&]() noexcept {
                for (auto const &p : devs) {
                    std::filesystem::remove(p);
                }
            });
            storage_pool::creation_flags flags;
            flags.interleave_chunks_evenly = enable_interleaving;
            storage_pool pool(
                devs, storage_pool::mode::create_if_needed, flags);
            std::array<size_t, 3> counts{0, 0, 0};
            std::array<std::vector<size_t>, 3> indices;
            for (size_t n = 0; n < pool.chunks(storage_pool::seq); n++) {
                auto &p =
                    pool.chunk(storage_pool::seq, static_cast<uint32_t>(n));
                auto const device_idx = static_cast<unsigned long>(
                    &p.device() - pool.devices().data());
                counts[device_idx]++;
                indices[device_idx].push_back(n);
            }
            EXPECT_EQ(counts[0], 19);
            EXPECT_EQ(counts[1], 9);
            EXPECT_EQ(counts[2], 4);
            std::cout << "\n   Device 0 appears at";
            for (size_t n = 0; n < indices[0].size(); n++) {
                std::cout << " " << indices[0][n];
                if (n > 0) {
                    gaps[0].push_back(indices[0][n] - indices[0][n - 1]);
                    EXPECT_LE(gaps[0].back(), 3);
                }
            }
            std::cout << "\n   Device 1 appears at";
            for (size_t n = 0; n < indices[1].size(); n++) {
                std::cout << " " << indices[1][n];
                if (n > 0) {
                    gaps[1].push_back(indices[1][n] - indices[1][n - 1]);
                    EXPECT_LE(gaps[1].back(), 5);
                }
            }
            std::cout << "\n   Device 2 appears at";
            for (size_t n = 0; n < indices[2].size(); n++) {
                std::cout << " " << indices[2][n];
                if (n > 0) {
                    gaps[2].push_back(indices[2][n] - indices[2][n - 1]);
                    EXPECT_LE(gaps[2].back(), 8);
                }
            }
            std::cout << "\n";
        };
        auto print_stddev = [](size_t devid, std::vector<size_t> const &vals) {
            double mean = 0;
            for (auto const &i : vals) {
                mean += static_cast<double>(i);
            }
            mean /= static_cast<double>(vals.size());
            double variance = 0;
            for (auto const &i : vals) {
                variance += pow(static_cast<double>(i) - mean, 2);
            }
            variance /= static_cast<double>(vals.size());
            std::cout << "\n   Device " << devid
                      << " incidence gap mean = " << mean
                      << " stddev = " << sqrt(variance)
                      << " 95% confidence interval = +/- "
                      << (1.96 * sqrt(variance) / sqrt(double(vals.size())))
                      << std::endl;
            return std::pair{mean, variance};
        };
        // Default is non-interleaved
        std::cout << "Checking the default is NOT interleaved chunks ...";
        do_test(false);
        auto stats = print_stddev(0, gaps[0]);
        EXPECT_EQ(stats.first, 1);
        EXPECT_EQ(stats.second, 0);
        stats = print_stddev(1, gaps[1]);
        EXPECT_EQ(stats.first, 1);
        EXPECT_EQ(stats.second, 0);
        stats = print_stddev(2, gaps[2]);
        EXPECT_EQ(stats.first, 1);
        EXPECT_EQ(stats.second, 0);

        // Set interleaved
        std::cout
            << "\n\nChecking turning on interleaved chunks does do so ...";
        do_test(true);
        stats = print_stddev(0, gaps[0]);
        EXPECT_GE(stats.first, 1.6);
        EXPECT_GE(stats.second, 0.45);
        stats = print_stddev(1, gaps[1]);
        EXPECT_GE(stats.first, 3.5);
        EXPECT_GE(stats.second, 0.75);
        stats = print_stddev(2, gaps[2]);
        EXPECT_GE(stats.first, 8);
    }

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
        static constexpr file_offset_t BLKSIZE = 256 * 1024 * 1024;
        std::filesystem::path devs[] = {
            create_temp_file(20 * BLKSIZE),
            create_temp_file(10 * BLKSIZE),
            create_temp_file(5 * BLKSIZE)};
        auto const undevs = monad::make_scope_exit([&]() noexcept {
            for (auto const &p : devs) {
                std::filesystem::remove(p);
            }
        });
        {
            storage_pool const _{devs};
        }
        std::filesystem::path const devs2[] = {devs[0], devs[1]};
        ASSERT_DEATH(
            storage_pool{devs2},
            "was initialised with a configuration different to this storage "
            "pool");
        storage_pool{devs2, storage_pool::mode::truncate};
    }

    TEST(StoragePool, config_hash_formula_is_pinned)
    {
        using monad::async::test::StoragePoolConfigHashInput;
        using monad::async::test::StoragePoolTestAccess;

        // Fixed, hardcoded inputs -- not read from a real device, whose
        // unique_hash varies by inode and filesystem -- so this test isolates
        // compute_config_hash_ itself. This value pins the on-disk format:
        // changing it means every existing pool becomes unopenable.
        StoragePoolConfigHashInput const devices[] = {
            {0x1122334455667788ULL, 4091, 1u << 28},
            {0xaabbccddeeff0011ULL, 39, 1u << 26},
        };
        EXPECT_EQ(
            StoragePoolTestAccess::compute_config_hash(devices), 0xbc17f0ecu);
    }

    TEST(StoragePool, add_devices_preserves_chunk_ids)
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
        static constexpr file_offset_t BLKSIZE = 256 * 1024 * 1024;
        std::filesystem::path devs[] = {
            create_temp_file(20 * BLKSIZE),
            create_temp_file(10 * BLKSIZE),
            create_temp_file(5 * BLKSIZE)};
        auto const undevs = monad::make_scope_exit([&]() noexcept {
            for (auto const &p : devs) {
                std::filesystem::remove(p);
            }
        });

        // A chunk's physical identity, independent of the pool object that
        // produced it.
        struct chunk_identity
        {
            size_t device_idx;
            file_offset_t read_offset;
            file_offset_t capacity;

            bool operator==(chunk_identity const &) const = default;
        };

        auto sample_chunks = [](storage_pool &pool,
                                storage_pool::chunk_type which) {
            std::vector<chunk_identity> ret;
            for (size_t n = 0; n < pool.chunks(which); n++) {
                auto &c = pool.chunk(which, static_cast<uint32_t>(n));
                ret.push_back(chunk_identity{
                    static_cast<size_t>(&c.device() - pool.devices().data()),
                    c.read_fd().second,
                    c.capacity()});
            }
            return ret;
        };

        std::vector<chunk_identity> seq_before;
        std::vector<chunk_identity> cnv_before;
        std::filesystem::path const two[] = {devs[0], devs[1]};
        {
            storage_pool pool{two};
            seq_before = sample_chunks(pool, storage_pool::seq);
            cnv_before = sample_chunks(pool, storage_pool::cnv);
        }
        ASSERT_GT(seq_before.size(), 0u);

        storage_pool pool{devs, storage_pool::mode::add_devices};
        EXPECT_TRUE(pool.is_adding_devices());
        EXPECT_FALSE(pool.is_newly_truncated());
        auto const seq_after = sample_chunks(pool, storage_pool::seq);
        auto const cnv_after = sample_chunks(pool, storage_pool::cnv);

        // Every pre-existing id keeps its exact physical meaning.
        ASSERT_GT(seq_after.size(), seq_before.size());
        ASSERT_GT(cnv_after.size(), cnv_before.size());
        for (size_t n = 0; n < seq_before.size(); n++) {
            EXPECT_EQ(seq_before[n], seq_after[n]) << "seq id " << n;
        }
        for (size_t n = 0; n < cnv_before.size(); n++) {
            EXPECT_EQ(cnv_before[n], cnv_after[n]) << "cnv id " << n;
        }
        // The added ids all live on the joining device.
        for (size_t n = seq_before.size(); n < seq_after.size(); n++) {
            EXPECT_EQ(seq_after[n].device_idx, 2u);
        }
        EXPECT_FALSE(pool.devices()[0].is_freshly_initialised());
        EXPECT_FALSE(pool.devices()[1].is_freshly_initialised());
        EXPECT_TRUE(pool.devices()[2].is_freshly_initialised());
    }

    TEST(StoragePool, add_devices_refusals)
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
        static constexpr file_offset_t BLKSIZE = 256 * 1024 * 1024;
        std::filesystem::path devs[] = {
            create_temp_file(20 * BLKSIZE),
            create_temp_file(10 * BLKSIZE),
            create_temp_file(5 * BLKSIZE),
            create_temp_file(4 * BLKSIZE)};
        auto const undevs = monad::make_scope_exit([&]() noexcept {
            for (auto const &p : devs) {
                std::filesystem::remove(p);
            }
        });
        std::filesystem::path const two[] = {devs[0], devs[1]};
        {
            storage_pool const _{two};
        }

        EXPECT_TRUE(storage_pool::has_pool_metadata(devs[0]));
        EXPECT_FALSE(storage_pool::has_pool_metadata(devs[2]));

        {
            std::filesystem::path const reordered[] = {
                devs[1], devs[0], devs[2]};
            ASSERT_DEATH(
                storage_pool(reordered, storage_pool::mode::add_devices),
                "must be listed first, in the exact order");
        }
        {
            std::filesystem::path const missing[] = {devs[0], devs[2]};
            ASSERT_DEATH(
                storage_pool(missing, storage_pool::mode::add_devices),
                "must be listed first, in the exact order");
        }
        {
            std::filesystem::path const joining_first[] = {
                devs[0], devs[2], devs[1]};
            ASSERT_DEATH(
                storage_pool(joining_first, storage_pool::mode::add_devices),
                "Devices being added must come last");
        }
        {
            std::filesystem::path const blank_first[] = {
                devs[2], devs[0], devs[1]};
            ASSERT_DEATH(
                storage_pool(blank_first, storage_pool::mode::add_devices),
                "cannot be the first source");
        }
        {
            storage_pool::creation_flags interleaved;
            interleaved.interleave_chunks_evenly = true;
            std::filesystem::path const three[] = {devs[0], devs[1], devs[2]};
            ASSERT_DEATH(
                storage_pool(
                    three, storage_pool::mode::add_devices, interleaved),
                "evenly interleaved pool");
        }

        // Every rejection above must have left devs[2] untouched, so a real
        // add still works afterwards.
        std::filesystem::path const three[] = {devs[0], devs[1], devs[2]};
        {
            storage_pool const pool{three, storage_pool::mode::add_devices};
            EXPECT_TRUE(pool.devices()[2].is_freshly_initialised());
        }
        // The grown pool now demands all three devices.
        {
            storage_pool const _{three};
        }
        ASSERT_DEATH(
            storage_pool{two},
            "was initialised with a configuration different");
        // A device carrying another pool's footer is refused: it classifies as
        // pre-existing, and its stored hash is neither this pool's nor the one
        // the add would produce.
        {
            std::filesystem::path const other[] = {devs[3]};
            {
                storage_pool const _{other};
            }
            std::filesystem::path const four[] = {
                devs[0], devs[1], devs[2], devs[3]};
            ASSERT_DEATH(
                storage_pool(four, storage_pool::mode::add_devices),
                "which is neither the hash of the sources listed");
        }
    }

    TEST(StoragePool, add_devices_rerun_completes_an_interrupted_add)
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
        static constexpr file_offset_t BLKSIZE = 256 * 1024 * 1024;
        std::filesystem::path devs[] = {
            create_temp_file(20 * BLKSIZE), create_temp_file(10 * BLKSIZE)};
        auto const undevs = monad::make_scope_exit([&]() noexcept {
            for (auto const &p : devs) {
                std::filesystem::remove(p);
            }
        });
        std::filesystem::path const one[] = {devs[0]};
        {
            storage_pool const _{one};
        }

        size_t chunks_after_add = 0;
        {
            storage_pool const pool{devs, storage_pool::mode::add_devices};
            chunks_after_add = pool.chunks(storage_pool::seq);
            EXPECT_TRUE(pool.devices()[1].is_freshly_initialised());
        }

        // The same command again, as an operator would run it to finish an add
        // interrupted after this point: the join is recognised, nothing is
        // reinitialised, and the pool is unchanged.
        storage_pool const pool{devs, storage_pool::mode::add_devices};
        EXPECT_EQ(pool.chunks(storage_pool::seq), chunks_after_add);
        EXPECT_FALSE(pool.devices()[0].is_freshly_initialised());
        EXPECT_FALSE(pool.devices()[1].is_freshly_initialised());
    }

    TEST(StoragePool, add_devices_refuses_a_set_the_metadata_cannot_describe)
    {
        using monad::async::test::StoragePoolAddDevicesInput;
        using monad::async::test::StoragePoolTestAccess;

        std::filesystem::path const sources[] = {
            "existing-device", "joining-device"};

        // A budget the size of MONAD008's, which the pool only does
        // arithmetic with: a 2Mb chunk capacity leaves 1Mb of database
        // metadata, which this header and 8 bytes per chunk exhaust at about
        // 65000 chunks.
        static constexpr storage_pool::db_metadata_budget budget{
            .header_bytes = 528512, .bytes_per_chunk = 8};
        static constexpr file_offset_t TWO_MB = 2 * 1024 * 1024;
        StoragePoolAddDevicesInput const beyond_metadata[] = {
            {.has_pool_metadata = true,
             .size = 100 * TWO_MB,
             .chunk_capacity = uint32_t(TWO_MB),
             .num_cnv_chunks = 3,
             .config_hash = 1,
             .chunks = 100},
            {.has_pool_metadata = false,
             .size = 70000 * TWO_MB,
             .chunk_capacity = 0,
             .num_cnv_chunks = 0,
             .config_hash = 0,
             .chunks = 0}};
        ASSERT_DEATH(
            StoragePoolTestAccess::validate_devices_to_add(
                sources, beyond_metadata, budget),
            "chunk capacity is too small");

        // At the 256Mb default the metadata budget is ample, so the 20 bit
        // chunk id space binds first.
        static constexpr file_offset_t CHUNK = 256 * 1024 * 1024;
        StoragePoolAddDevicesInput const beyond_id_space[] = {
            {.has_pool_metadata = true,
             .size = 100 * CHUNK,
             .chunk_capacity = uint32_t(CHUNK),
             .num_cnv_chunks = 3,
             .config_hash = 1,
             .chunks = 100},
            {.has_pool_metadata = false,
             .size = 1100000 * CHUNK,
             .chunk_capacity = 0,
             .num_cnv_chunks = 0,
             .config_hash = 0,
             .chunks = 0}};
        ASSERT_DEATH(
            StoragePoolTestAccess::validate_devices_to_add(
                sources, beyond_id_space, budget),
            "20 bit chunk id space");
    }

    TEST(StoragePool, add_devices_rejects_undersized_joining_device)
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
        static constexpr file_offset_t BLKSIZE = 256 * 1024 * 1024;
        std::filesystem::path devs[] = {
            create_temp_file(20 * BLKSIZE),
            create_temp_file(10 * BLKSIZE),
            // 3 chunks at the default 256Mb chunk capacity; the default pool
            // needs num_cnv_chunks(3) + 1 = 4.
            create_temp_file(3 * BLKSIZE)};
        auto const undevs = monad::make_scope_exit([&]() noexcept {
            for (auto const &p : devs) {
                std::filesystem::remove(p);
            }
        });
        std::filesystem::path const two[] = {devs[0], devs[1]};
        {
            storage_pool const _{two};
        }

        std::filesystem::path const three[] = {devs[0], devs[1], devs[2]};
        ASSERT_DEATH(
            storage_pool(three, storage_pool::mode::add_devices),
            "would have only");

        // Left byte-for-byte untouched by the rejected attempt: still
        // classifies as blank, so the exact same path can be retried once it
        // is large enough.
        EXPECT_FALSE(storage_pool::has_pool_metadata(devs[2]));
        MONAD_ASSERT(
            -1 !=
            ::truncate(
                devs[2].c_str(), static_cast<off_t>(5 * BLKSIZE + 16384)));

        storage_pool const pool{three, storage_pool::mode::add_devices};
        EXPECT_TRUE(pool.devices()[2].is_freshly_initialised());
    }

    TEST(StoragePool, add_devices_rejects_a_grown_device_with_data)
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
        static constexpr file_offset_t BLKSIZE = 256 * 1024 * 1024;
        std::filesystem::path devs[] = {
            create_temp_file(20 * BLKSIZE),
            create_temp_file(10 * BLKSIZE),
            create_temp_file(20 * BLKSIZE)};
        auto const undevs = monad::make_scope_exit([&]() noexcept {
            for (auto const &p : devs) {
                std::filesystem::remove(p);
            }
        });
        std::filesystem::path const two[] = {devs[0], devs[1]};
        {
            storage_pool const _{two};
        }

        // Models an LVM-grown device: real data sits well past chunk 0 (the
        // one chunk on a non-first device that is never written, so probing
        // only it would miss this), yet the device's footer no longer sits
        // at the end, so it still classifies as blank.
        static constexpr size_t mid_chunk = 10;
        std::vector<std::byte> const marker(64, std::byte{0x5a});
        {
            int const fd = ::open(devs[2].c_str(), O_WRONLY);
            ASSERT_NE(fd, -1);
            auto const unfd =
                monad::make_scope_exit([fd]() noexcept { ::close(fd); });
            ASSERT_EQ(
                ssize_t(marker.size()),
                ::pwrite(
                    fd,
                    marker.data(),
                    marker.size(),
                    static_cast<off_t>(mid_chunk * BLKSIZE)));
        }
        EXPECT_FALSE(storage_pool::has_pool_metadata(devs[2]));

        std::filesystem::path const three[] = {devs[0], devs[1], devs[2]};
        ASSERT_DEATH(
            storage_pool(three, storage_pool::mode::add_devices),
            "is not blank");

        // Left untouched by the rejection: still blank by the footer test,
        // and the data planted mid-device is still there.
        EXPECT_FALSE(storage_pool::has_pool_metadata(devs[2]));
        std::vector<std::byte> readback(marker.size());
        int const fd = ::open(devs[2].c_str(), O_RDONLY);
        ASSERT_NE(fd, -1);
        auto const unfd =
            monad::make_scope_exit([fd]() noexcept { ::close(fd); });
        ASSERT_EQ(
            ssize_t(readback.size()),
            ::pread(
                fd,
                readback.data(),
                readback.size(),
                static_cast<off_t>(mid_chunk * BLKSIZE)));
        EXPECT_EQ(0, memcmp(marker.data(), readback.data(), marker.size()));
    }

    TEST(StoragePool, rejects_duplicate_path)
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
        static constexpr file_offset_t BLKSIZE = 256 * 1024 * 1024;
        std::filesystem::path devs[] = {
            create_temp_file(20 * BLKSIZE), create_temp_file(10 * BLKSIZE)};
        auto const undevs = monad::make_scope_exit([&]() noexcept {
            for (auto const &p : devs) {
                std::filesystem::remove(p);
            }
        });
        std::filesystem::path const one[] = {devs[0]};
        {
            storage_pool const _{one};
        }

        std::filesystem::path const duplicated[] = {devs[0], devs[1], devs[1]};
        ASSERT_DEATH(
            storage_pool(duplicated, storage_pool::mode::add_devices),
            "name the same underlying device");
        EXPECT_FALSE(storage_pool::has_pool_metadata(devs[1]));

        // A hard link to the same file: identical (dev, ino), different path
        // spelling, and no on-disk footer to distinguish them either.
        std::filesystem::path const linked = devs[1].string() + "_hardlink";
        std::filesystem::create_hard_link(devs[1], linked);
        auto const unlinked = monad::make_scope_exit(
            [&]() noexcept { ::unlink(linked.c_str()); });
        std::filesystem::path const via_link[] = {devs[0], devs[1], linked};
        ASSERT_DEATH(
            storage_pool(via_link, storage_pool::mode::add_devices),
            "name the same underlying device");
        EXPECT_FALSE(storage_pool::has_pool_metadata(devs[1]));

        // The refusal is not particular to mode::add_devices: two sources
        // naming one device would alias the same storage under two chunk id
        // ranges whichever mode reached them, and creating is where an
        // operator is most likely to mistype a list.
        std::filesystem::path const twice[] = {devs[1], devs[1]};
        for (auto const mode :
             {storage_pool::mode::create_if_needed,
              storage_pool::mode::truncate,
              storage_pool::mode::open_existing}) {
            ASSERT_DEATH(
                storage_pool(twice, mode), "name the same underlying device");
        }
        EXPECT_FALSE(storage_pool::has_pool_metadata(devs[1]))
            << "a refused create initialised the device anyway";
        ASSERT_DEATH(
            storage_pool(via_link, storage_pool::mode::create_if_needed),
            "name the same underlying device");

        // Left untouched by every rejection: a real add with a single,
        // genuinely distinct joining device still works afterwards.
        std::filesystem::path const two[] = {devs[0], devs[1]};
        storage_pool const pool{two, storage_pool::mode::add_devices};
        EXPECT_TRUE(pool.devices()[1].is_freshly_initialised());
    }

    TEST(StoragePool, add_devices_inherits_pool_geometry)
    {
        // This test's flag mismatch on an existing device reaches the
        // num_cnv_chunks LOG_WARNING in make_device_, which dereferences the
        // global root logger; this test binary's plain gtest_main never
        // initialises it.
        monad::start_logger_minimal();
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
        static constexpr file_offset_t BLKSIZE = 64 * 1024 * 1024;
        std::filesystem::path devs[] = {
            create_temp_file(20 * BLKSIZE), create_temp_file(10 * BLKSIZE)};
        auto const undevs = monad::make_scope_exit([&]() noexcept {
            for (auto const &p : devs) {
                std::filesystem::remove(p);
            }
        });
        storage_pool::creation_flags created;
        created.set_chunk_capacity(26); // 64Mb, not the 256Mb default
        created.num_cnv_chunks = 4;
        std::filesystem::path const one[] = {devs[0]};
        {
            storage_pool const _{
                one, storage_pool::mode::create_if_needed, created};
        }

        // Deliberately disagree with the pool on both geometry values.
        storage_pool::creation_flags wrong;
        wrong.set_chunk_capacity(28);
        wrong.num_cnv_chunks = 9;
        storage_pool const pool{devs, storage_pool::mode::add_devices, wrong};
        EXPECT_EQ(pool.devices()[1].cnv_chunks(), 4u);
        // 64Mb chunks, so a 10 * 64Mb device yields about 10 chunks, not 2.
        EXPECT_GE(pool.devices()[1].chunks(), 9u);
    }

    // Reproduces exactly what lvextend leaves behind: a pool built on a
    // device, closed, then the device made larger. Its footer is stranded
    // mid-device and its per-chunk bytes-used array, the only on-disk record
    // of how full each existing chunk is, has to survive the move.
    TEST(StoragePool, grow_last_device_preserves_chunks_and_bytes_used)
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
        static constexpr file_offset_t BLKSIZE = 256 * 1024 * 1024;
        std::filesystem::path const devs[] = {
            create_temp_file(20 * BLKSIZE), create_temp_file(10 * BLKSIZE)};
        auto const undevs = monad::make_scope_exit([&]() noexcept {
            for (auto const &p : devs) {
                std::filesystem::remove(p);
            }
        });

        // seq chunk id -> bytes written into it, and where that chunk lives.
        std::vector<std::pair<uint32_t, uint32_t>> written;
        std::vector<std::pair<size_t, file_offset_t>> placement;
        size_t chunks_before = 0;
        {
            storage_pool pool{devs};
            chunks_before = pool.chunks(storage_pool::seq);
            ASSERT_GT(chunks_before, 20u);
            // Spanning both devices, and including chunks on the device about
            // to grow so that it is not blank.
            for (uint32_t const id : {0u, 5u, 17u, 20u}) {
                ASSERT_LT(id, chunks_before);
                auto const bytes = static_cast<uint32_t>(4096 * (id + 1));
                std::vector<std::byte> buffer(bytes, std::byte{0xa5});
                auto &chunk = pool.chunk(storage_pool::seq, id);
                auto const fd = chunk.write_fd(bytes);
                ASSERT_EQ(
                    ssize_t(bytes),
                    ::pwrite(
                        fd.first,
                        buffer.data(),
                        bytes,
                        static_cast<off_t>(fd.second)));
                written.emplace_back(id, bytes);
            }
            for (uint32_t id = 0; id < chunks_before; id++) {
                auto const &chunk = pool.chunk(storage_pool::seq, id);
                size_t device_index = 0;
                for (size_t n = 0; n < pool.devices().size(); n++) {
                    if (&pool.devices()[n] == &chunk.device()) {
                        device_index = n;
                    }
                }
                placement.emplace_back(device_index, chunk.read_fd().second);
            }
        }

        // The extend itself. Nothing writes pool metadata at the new end, so
        // the pool now presents no footer there at all.
        auto const recorded =
            static_cast<file_offset_t>(std::filesystem::file_size(devs[1]));
        {
            int const fd = ::open(devs[1].c_str(), O_RDWR);
            ASSERT_NE(fd, -1);
            auto const unfd =
                monad::make_scope_exit([fd]() noexcept { ::close(fd); });
            ASSERT_NE(
                -1, ::ftruncate(fd, static_cast<off_t>(14 * BLKSIZE + 16384)));
        }
        EXPECT_FALSE(storage_pool::has_pool_metadata(devs[1]));
        storage_pool::creation_flags flags;
        flags.recorded_size_of_grown_device = recorded;

        auto const check = [&](storage_pool &pool) {
            EXPECT_GT(pool.chunks(storage_pool::seq), chunks_before);
            for (uint32_t id = 0; id < chunks_before; id++) {
                auto const &chunk = pool.chunk(storage_pool::seq, id);
                size_t device_index = 0;
                for (size_t n = 0; n < pool.devices().size(); n++) {
                    if (&pool.devices()[n] == &chunk.device()) {
                        device_index = n;
                    }
                }
                EXPECT_EQ(device_index, placement[id].first) << "chunk " << id;
                EXPECT_EQ(chunk.read_fd().second, placement[id].second)
                    << "chunk " << id;
            }
            for (auto const &[id, bytes] : written) {
                EXPECT_EQ(pool.chunk(storage_pool::seq, id).size(), bytes)
                    << "chunk " << id;
            }
            for (auto id = static_cast<uint32_t>(chunks_before);
                 id < pool.chunks(storage_pool::seq);
                 id++) {
                EXPECT_EQ(pool.chunk(storage_pool::seq, id).size(), 0u)
                    << "new chunk " << id;
            }
        };

        {
            storage_pool pool{devs, storage_pool::mode::add_devices, flags};
            EXPECT_FALSE(pool.devices()[1].is_freshly_initialised())
                << "the grown device was wiped rather than relocated";
            check(pool);
        }
        // And the relocation is durable: a plain open sees the same pool.
        storage_pool pool{devs, storage_pool::mode::open_existing};
        check(pool);
    }

    // Fixture for the grow tests: builds a pool, writes a known amount into
    // one seq chunk of the last device so it is not blank, and can then
    // extend that device in place.
    struct growable_pool
    {
        static constexpr file_offset_t BLKSIZE = 256 * 1024 * 1024;
        static constexpr uint32_t MARKED_BYTES = 40960;

        std::vector<std::filesystem::path> devs;
        uint32_t marked_chunk{0};
        size_t chunks_before{0};
        // What db_metadata recorded for the device these tests grow, i.e. its
        // size as of the pool open the constructor performed.
        file_offset_t recorded_last_size{0};

        explicit growable_pool(std::vector<file_offset_t> const &lengths)
        {
            for (auto const length : lengths) {
                monad::test::remove_stale_temp_files_once(
                    working_temporary_directory(), "monad_storage_pool_test_");
                std::filesystem::path path(
                    working_temporary_directory() /
                    "monad_storage_pool_test_XXXXXX");
                int const fd = ::mkstemp((char *)path.native().data());
                MONAD_ASSERT(fd != -1);
                MONAD_ASSERT(
                    -1 != ::ftruncate(fd, static_cast<off_t>(length + 16384)));
                ::close(fd);
                devs.push_back(std::move(path));
            }
            storage_pool pool{devs};
            chunks_before = pool.chunks(storage_pool::seq);
            // The last seq chunk always lives on the last device, which is
            // the one these tests grow. Chunk 0 is written too: a live pool
            // always carries db_metadata on device 0, so a device 0 reading
            // as entirely blank is not a state worth modelling.
            marked_chunk = static_cast<uint32_t>(chunks_before - 1);
            for (uint32_t const id : {0u, marked_chunk}) {
                std::vector<std::byte> buffer(MARKED_BYTES, std::byte{0xa5});
                auto &chunk = pool.chunk(storage_pool::seq, id);
                auto const fd = chunk.write_fd(MARKED_BYTES);
                MONAD_ASSERT(
                    ssize_t(MARKED_BYTES) ==
                    ::pwrite(
                        fd.first,
                        buffer.data(),
                        MARKED_BYTES,
                        static_cast<off_t>(fd.second)));
            }
            recorded_last_size = last_size();
        }

        growable_pool(growable_pool const &) = delete;
        growable_pool &operator=(growable_pool const &) = delete;

        ~growable_pool()
        {
            for (auto const &p : devs) {
                std::filesystem::remove(p);
            }
        }

        void extend_last_to(file_offset_t const size) const
        {
            int const fd = ::open(devs.back().c_str(), O_RDWR);
            MONAD_ASSERT(fd != -1);
            auto const unfd =
                monad::make_scope_exit([fd]() noexcept { ::close(fd); });
            MONAD_ASSERT(-1 != ::ftruncate(fd, static_cast<off_t>(size)));
        }

        file_offset_t last_size() const
        {
            return static_cast<file_offset_t>(
                std::filesystem::file_size(devs.back()));
        }

        // What monad-mpt hands the pool: only the recorded size can locate the
        // metadata an extend stranded, so a grow is refused without it.
        storage_pool::creation_flags recorded_flags() const
        {
            storage_pool::creation_flags flags;
            flags.recorded_size_of_grown_device = recorded_last_size;
            return flags;
        }
    };

    // The motivating case: one logical volume, extended in place. There is no
    // sibling to cross-check the recorded previous size against, so it is
    // validated against the stranded footer's own config_hash.
    TEST(StoragePool, grow_single_device_pool)
    {
        growable_pool fixture{{10 * growable_pool::BLKSIZE}};
        fixture.extend_last_to(14 * growable_pool::BLKSIZE + 16384);

        storage_pool pool{
            fixture.devs,
            storage_pool::mode::add_devices,
            fixture.recorded_flags()};
        EXPECT_GT(pool.chunks(storage_pool::seq), fixture.chunks_before);
        EXPECT_FALSE(pool.devices()[0].is_freshly_initialised());
        EXPECT_EQ(
            pool.chunk(storage_pool::seq, fixture.marked_chunk).size(),
            growable_pool::MARKED_BYTES);
    }

    // New chunks splice onto the tail of the free list, so a device the pool
    // already owns can still have nothing on it at all. Every chunk then
    // reads as blank, exactly like a device being joined, and only the
    // recorded previous size tells the two apart.
    TEST(StoragePool, grow_an_empty_member_device)
    {
        static constexpr file_offset_t BLKSIZE = growable_pool::BLKSIZE;
        auto make = [](file_offset_t length) -> std::filesystem::path {
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
        std::filesystem::path const devs[] = {
            make(20 * BLKSIZE), make(10 * BLKSIZE)};
        auto const undevs = monad::make_scope_exit([&]() noexcept {
            for (auto const &p : devs) {
                std::filesystem::remove(p);
            }
        });

        size_t chunks_before = 0;
        {
            storage_pool pool{devs};
            chunks_before = pool.chunks(storage_pool::seq);
            // Device 0 only; device 1 is left with not one byte written.
            std::vector<std::byte> buffer(40960, std::byte{0xa5});
            auto &chunk = pool.chunk(storage_pool::seq, 0);
            auto const fd =
                chunk.write_fd(static_cast<uint32_t>(buffer.size()));
            ASSERT_EQ(
                ssize_t(buffer.size()),
                ::pwrite(
                    fd.first,
                    buffer.data(),
                    buffer.size(),
                    static_cast<off_t>(fd.second)));
        }
        auto const recorded =
            static_cast<file_offset_t>(std::filesystem::file_size(devs[1]));
        {
            int const fd = ::open(devs[1].c_str(), O_RDWR);
            ASSERT_NE(fd, -1);
            auto const unfd =
                monad::make_scope_exit([fd]() noexcept { ::close(fd); });
            ASSERT_NE(-1, ::ftruncate(fd, static_cast<off_t>(14 * BLKSIZE)));
        }

        storage_pool::creation_flags flags;
        flags.recorded_size_of_grown_device = recorded;
        {
            storage_pool const pool{
                devs, storage_pool::mode::add_devices, flags};
            EXPECT_FALSE(pool.devices()[1].is_freshly_initialised())
                << "an empty member device was rejoined as a new one";
            EXPECT_GT(pool.chunks(storage_pool::seq), chunks_before);
        }
        storage_pool const pool{devs, storage_pool::mode::open_existing};
        EXPECT_GT(pool.chunks(storage_pool::seq), chunks_before);
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
        growable_pool fixture{{10 * growable_pool::BLKSIZE}};
        fixture.extend_last_to(14 * growable_pool::BLKSIZE + 16384);
        {
            storage_pool pool{
                fixture.devs,
                storage_pool::mode::add_devices,
                fixture.recorded_flags()};
            ASSERT_EQ(
                pool.chunk(storage_pool::seq, fixture.marked_chunk).size(),
                growable_pool::MARKED_BYTES);
        }

        auto const size = fixture.last_size();
        {
            int const fd = ::open(fixture.devs[0].c_str(), O_RDWR);
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
        ASSERT_FALSE(storage_pool::has_pool_metadata(fixture.devs[0]))
            << "the crash window was not built";

        // Re-running redoes the whole operation from the stranded footer,
        // which this never touched.
        storage_pool pool{
            fixture.devs,
            storage_pool::mode::add_devices,
            fixture.recorded_flags()};
        EXPECT_GT(pool.chunks(storage_pool::seq), fixture.chunks_before);
        EXPECT_EQ(
            pool.chunk(storage_pool::seq, fixture.marked_chunk).size(),
            growable_pool::MARKED_BYTES);
    }

    // A device can be extended again after a completed grow, and what the
    // second run must be given is the size the first one left it at.
    TEST(StoragePool, grow_twice_in_succession)
    {
        growable_pool fixture{{10 * growable_pool::BLKSIZE}};
        fixture.extend_last_to(12 * growable_pool::BLKSIZE + 16384);
        size_t after_first = 0;
        {
            storage_pool const pool{
                fixture.devs,
                storage_pool::mode::add_devices,
                fixture.recorded_flags()};
            after_first = pool.chunks(storage_pool::seq);
        }
        ASSERT_GT(after_first, fixture.chunks_before);

        // That run was a writable open, so this is what the database now
        // records for the device.
        auto const recorded = fixture.last_size();
        fixture.extend_last_to(15 * growable_pool::BLKSIZE + 16384);
        storage_pool::creation_flags flags;
        flags.recorded_size_of_grown_device = recorded;
        storage_pool pool{fixture.devs, storage_pool::mode::add_devices, flags};
        EXPECT_GT(pool.chunks(storage_pool::seq), after_first);
        EXPECT_EQ(
            pool.chunk(storage_pool::seq, fixture.marked_chunk).size(),
            growable_pool::MARKED_BYTES);
    }

    // The new metadata region must clear the old one, or writing it would
    // destroy the bytes-used array before the new footer is durable.
    TEST(StoragePool, grow_too_small_to_clear_the_old_metadata_is_refused)
    {
        growable_pool fixture{{10 * growable_pool::BLKSIZE}};
        // The region is only 64 bytes plus four per chunk, so this refusal
        // takes a growth far below anything an operator would ask for; it
        // exists to keep the crash window closed, not to reject real input.
        auto const before = fixture.last_size();
        fixture.extend_last_to(before + 64);

        ASSERT_DEATH(
            storage_pool(
                fixture.devs,
                storage_pool::mode::add_devices,
                fixture.recorded_flags()),
            "would overwrite the metadata being recovered");
        // Refused before anything was written: the stranded footer is still
        // the only one on the device.
        EXPECT_FALSE(storage_pool::has_pool_metadata(fixture.devs[0]));
    }

    // The recorded size is checked against the pool's own hash before it is
    // acted on, so a wrong one is refused rather than used. Four bytes
    // spelling MND0 turn up in trie data eventually, and this is what stops
    // one of them being taken for a footer.
    TEST(StoragePool, grow_with_a_wrong_recorded_size_is_refused)
    {
        growable_pool fixture{{10 * growable_pool::BLKSIZE}};
        fixture.extend_last_to(14 * growable_pool::BLKSIZE + 16384);

        storage_pool::creation_flags flags;
        flags.recorded_size_of_grown_device = fixture.recorded_last_size - 8192;
        ASSERT_DEATH(
            storage_pool(fixture.devs, storage_pool::mode::add_devices, flags),
            "nor any at the");
        EXPECT_FALSE(storage_pool::has_pool_metadata(fixture.devs[0]));
    }

    // Without the recorded size nothing can say where the extend left the
    // metadata, and the refusal has to say how to get one.
    TEST(StoragePool, grow_without_a_recorded_size_is_refused)
    {
        growable_pool fixture{{10 * growable_pool::BLKSIZE}};
        fixture.extend_last_to(14 * growable_pool::BLKSIZE + 16384);

        ASSERT_DEATH(
            storage_pool(fixture.devs, storage_pool::mode::add_devices),
            "must be opened writable once before its devices are extended");
        EXPECT_FALSE(storage_pool::has_pool_metadata(fixture.devs[0]));
    }

    // One operation reconciling the pool with everything the hardware now
    // offers: the last device the pool owns has grown, and a blank device
    // follows it. Both land under a single metadata growth.
    TEST(StoragePool, grow_and_append_in_one_operation)
    {
        growable_pool const fixture{
            {20 * growable_pool::BLKSIZE, 10 * growable_pool::BLKSIZE}};
        fixture.extend_last_to(14 * growable_pool::BLKSIZE + 16384);

        monad::test::remove_stale_temp_files_once(
            working_temporary_directory(), "monad_storage_pool_test_");
        std::filesystem::path joining(
            working_temporary_directory() / "monad_storage_pool_test_XXXXXX");
        int const fd = ::mkstemp((char *)joining.native().data());
        ASSERT_NE(fd, -1);
        ASSERT_NE(
            -1,
            ::ftruncate(
                fd, static_cast<off_t>(5 * growable_pool::BLKSIZE + 16384)));
        ::close(fd);
        auto const unjoining = monad::make_scope_exit(
            [&]() noexcept { std::filesystem::remove(joining); });

        std::vector<std::filesystem::path> all = fixture.devs;
        all.push_back(joining);
        {
            storage_pool pool{
                all, storage_pool::mode::add_devices, fixture.recorded_flags()};
            EXPECT_EQ(pool.devices().size(), 3u);
            EXPECT_FALSE(pool.devices()[1].is_freshly_initialised())
                << "the grown device was wiped rather than relocated";
            EXPECT_TRUE(pool.devices()[2].is_freshly_initialised());
            EXPECT_GT(pool.chunks(storage_pool::seq), fixture.chunks_before);
            EXPECT_EQ(
                pool.chunk(storage_pool::seq, fixture.marked_chunk).size(),
                growable_pool::MARKED_BYTES);
        }
        // Every device now agrees on the new hash, so a plain open succeeds.
        storage_pool pool{all, storage_pool::mode::open_existing};
        EXPECT_EQ(
            pool.chunk(storage_pool::seq, fixture.marked_chunk).size(),
            growable_pool::MARKED_BYTES);
    }

    // Growing device i renumbers every chunk on the devices after it, so only
    // the last device the pool owns may grow. The recorded size cannot
    // validate for such a device -- the hash it would have to match covers the
    // devices behind it too -- so the misplaced-device diagnosis has to be
    // reached before that failure is reported as a foreign device.
    TEST(StoragePool, grow_a_device_which_is_not_the_last_is_refused)
    {
        growable_pool fixture{
            {20 * growable_pool::BLKSIZE, 10 * growable_pool::BLKSIZE}};
        auto const recorded = static_cast<file_offset_t>(
            std::filesystem::file_size(fixture.devs[0]));
        // Extend device 0, which still has device 1 behind it.
        int const fd = ::open(fixture.devs[0].c_str(), O_RDWR);
        ASSERT_NE(fd, -1);
        auto const unfd =
            monad::make_scope_exit([fd]() noexcept { ::close(fd); });
        ASSERT_NE(
            -1,
            ::ftruncate(
                fd, static_cast<off_t>(24 * growable_pool::BLKSIZE + 16384)));

        storage_pool::creation_flags flags;
        flags.recorded_size_of_grown_device = recorded;
        ASSERT_DEATH(
            storage_pool(fixture.devs, storage_pool::mode::add_devices, flags),
            "Only the last device the pool already owns may be extended");
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
