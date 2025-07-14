#include "gtest/gtest.h"

#include <category/async/config.hpp>
#include <category/async/detail/scope_polyfill.hpp>
#include <category/async/storage_pool.hpp>
#include <category/async/util.hpp>
#include <monad/core/assert.h>
#include <monad/test/gtest_signal_stacktrace_printer.hpp> // NOLINT

#include <array>
#include <cmath>
#include <cstddef>
#include <cstdint>
#include <cstring>
#include <filesystem>
#include <iostream>
#include <stdexcept>
#include <system_error>
#include <utility>
#include <vector>

#include <stdlib.h>
#include <unistd.h>

namespace
{
    using namespace MONAD_ASYNC_NAMESPACE;

    inline void print_pool_statistics(storage_pool const &pool)
    {
        std::cout << "Pool has " << pool.devices().size() << " devices:";
        for (size_t n = 0; n < pool.devices().size(); n++) {
            auto const &device = pool.devices()[n];
            auto capacity = device.capacity();
            std::cout << "\n   " << (n + 1) << ". chunks = " << device.chunks()
                      << " capacity = " << capacity.first
                      << " used = " << capacity.second
                      << " path = " << device.current_path();
        }
        std::cout << "\n\n    Total conventional chunks = "
                  << pool.chunks(storage_pool::cnv) << " of which active = "
                  << pool.currently_active_chunks(storage_pool::cnv);
        std::cout << "\nTotal sequential write chunks = "
                  << pool.chunks(storage_pool::seq) << " of which active = "
                  << pool.currently_active_chunks(storage_pool::seq);
        std::cout << "\n   First conventional chunk ";
        if (auto chunk = pool.chunk(storage_pool::cnv, 0)) {
            std::cout << "has capacity = " << chunk->capacity()
                      << " used = " << chunk->size();
        }
        else {
            std::cout << "is not active";
        }
        std::cout << "\n   First sequential chunk ";
        if (auto chunk = pool.chunk(storage_pool::seq, 0)) {
            std::cout << "has capacity = " << chunk->capacity()
                      << " used = " << chunk->size();
        }
        else {
            std::cout << "is not active";
        }
        std::cout << std::endl;
    }

    inline void run_tests(storage_pool &pool)
    {
        print_pool_statistics(pool);
        std::cout << "\n\nActivating first conventional chunk ..." << std::endl;
        auto chunk1 = pool.activate_chunk(storage_pool::cnv, 0);
        print_pool_statistics(pool);
        std::cout << "\n\nActivating first sequential chunk ..." << std::endl;
        auto chunk2 = pool.activate_chunk(storage_pool::seq, 0);
        print_pool_statistics(pool);
        std::cout << "\n\nActivating last sequential chunk (which is "
                  << (pool.chunks(storage_pool::seq) - 1) << ") ..."
                  << std::endl;
        auto chunk3 = pool.activate_chunk(
            storage_pool::seq,
            static_cast<uint32_t>(pool.chunks(storage_pool::seq) - 1));
        print_pool_statistics(pool);

        std::vector<std::byte> buffer(1024 * 1024);
        memset(buffer.data(), 0xee, buffer.size());
        std::cout << "\n\nWriting to conventional chunk ..." << std::endl;
        EXPECT_EQ(chunk1->size(), chunk1->capacity()); // always full
        auto fd = chunk1->write_fd(buffer.size());
        EXPECT_EQ(fd.second, 0);
        MONAD_ASSERT(
            -1 != ::pwrite(
                      fd.first,
                      buffer.data(),
                      buffer.size(),
                      static_cast<off_t>(fd.second)));
        EXPECT_EQ(chunk1->size(), chunk1->capacity()); // always full

        memset(buffer.data(), 0xaa, buffer.size());
        fd = chunk1->write_fd(buffer.size());
        EXPECT_EQ(fd.second, 0);
        MONAD_ASSERT(
            -1 != ::pwrite(
                      fd.first,
                      buffer.data(),
                      buffer.size(),
                      static_cast<off_t>(fd.second + buffer.size())));
        EXPECT_EQ(chunk1->size(), chunk1->capacity()); // always full
        print_pool_statistics(pool);

        memset(buffer.data(), 0x77, buffer.size());
        std::cout << "\n\nWriting to first sequential chunk ..." << std::endl;
        fd = chunk2->write_fd(buffer.size());
        EXPECT_EQ(fd.second, chunk1->capacity() * 3);
        MONAD_ASSERT(
            -1 != ::pwrite(
                      fd.first,
                      buffer.data(),
                      buffer.size(),
                      static_cast<off_t>(fd.second)));
        EXPECT_EQ(chunk2->size(), buffer.size());
        print_pool_statistics(pool);

        memset(buffer.data(), 0x55, buffer.size());
        fd = chunk2->write_fd(buffer.size());
        EXPECT_EQ(fd.second, chunk1->capacity() * 3 + buffer.size());
        MONAD_ASSERT(
            -1 != ::pwrite(
                      fd.first,
                      buffer.data(),
                      buffer.size(),
                      static_cast<off_t>(fd.second)));
        EXPECT_EQ(chunk2->size(), buffer.size() * 2);
        print_pool_statistics(pool);

        memset(buffer.data(), 0x33, buffer.size());
        std::cout << "\n\nWriting to last sequential chunk ..." << std::endl;
        fd = chunk3->write_fd(buffer.size());
        EXPECT_EQ(
            fd.second,
            chunk1->capacity() * 2 + chunk1->capacity() *
                                         pool.chunks(storage_pool::seq) /
                                         pool.devices().size());
        MONAD_ASSERT(
            -1 != ::pwrite(
                      fd.first,
                      buffer.data(),
                      buffer.size(),
                      static_cast<off_t>(fd.second)));
        EXPECT_EQ(chunk3->size(), buffer.size());
        print_pool_statistics(pool);

        memset(buffer.data(), 0x22, buffer.size());
        fd = chunk3->write_fd(buffer.size());
        EXPECT_EQ(
            fd.second,
            chunk1->capacity() * 2 +
                chunk1->capacity() * pool.chunks(storage_pool::seq) /
                    pool.devices().size() +
                buffer.size());
        MONAD_ASSERT(
            -1 != ::pwrite(
                      fd.first,
                      buffer.data(),
                      buffer.size(),
                      static_cast<off_t>(fd.second)));
        EXPECT_EQ(chunk3->size(), buffer.size() * 2);
        print_pool_statistics(pool);

        std::vector<std::byte> buffer2(buffer.size());
        auto check = [&](auto &chunk, int a, int b) {
            auto fd = chunk->read_fd();
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
        chunk3->destroy_contents();
        EXPECT_EQ(chunk1->size(), chunk1->capacity()); // always full
        EXPECT_EQ(chunk2->size(), buffer.size() * 2);
        EXPECT_EQ(chunk3->size(), 0);
        check(chunk1, 0xee, 0xaa);
        check(chunk2, 0x77, 0x55);
        check(chunk3, 0x00, 0x00);
        print_pool_statistics(pool);

        std::cout << "\n\nDestroying contents of conventional chunk ..."
                  << std::endl;
        chunk1->destroy_contents();
        EXPECT_EQ(chunk1->size(), chunk1->capacity()); // always full
        EXPECT_EQ(chunk2->size(), buffer.size() * 2);
        EXPECT_EQ(chunk3->size(), 0);
        check(chunk1, 0x00, 0x00);
        check(chunk2, 0x77, 0x55);
        check(chunk3, 0x00, 0x00);
        print_pool_statistics(pool);

        std::cout << "\n\nDestroying contents of first sequential chunk ..."
                  << std::endl;
        chunk2->destroy_contents();
        EXPECT_EQ(chunk1->size(), chunk1->capacity()); // always full
        EXPECT_EQ(chunk2->size(), 0);
        EXPECT_EQ(chunk3->size(), 0);
        check(chunk1, 0x00, 0x00);
        check(chunk2, 0x00, 0x00);
        check(chunk3, 0x00, 0x00);
        print_pool_statistics(pool);

        std::cout << "\n\nReleasing chunks ..." << std::endl;
        chunk1.reset();
        chunk2.reset();
        chunk3.reset();
        print_pool_statistics(pool);
    }

    TEST(StoragePool, anonymous_inode)
    {
        storage_pool pool(use_anonymous_inode_tag{});
        run_tests(pool);
    }

    TEST(StoragePool, raw_partitions)
    {
        std::filesystem::path const devs[] = {
            "/dev/mapper/raid0-rawblk0", "/dev/mapper/raid0-rawblk1"};
        try {
            storage_pool pool(devs, storage_pool::mode::truncate);
            run_tests(pool);
        }
        catch (std::system_error const &e) {
            if (e.code() != std::errc::no_such_file_or_directory &&
                e.code() != std::errc::permission_denied) {
                throw;
            }
        }
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
            auto undevs = monad::make_scope_exit([&]() noexcept {
                for (auto &p : devs) {
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
                auto p = pool.activate_chunk(
                    storage_pool::seq, static_cast<uint32_t>(n));
                auto const device_idx = static_cast<unsigned long>(
                    &p->device() - pool.devices().data());
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
        auto undevs = monad::make_scope_exit([&]() noexcept {
            for (auto &p : devs) {
                std::filesystem::remove(p);
            }
        });
        {
            storage_pool const _{devs};
        }
        std::filesystem::path const devs2[] = {devs[0], devs[1]};
        EXPECT_THROW(storage_pool{devs2}, std::runtime_error);
        storage_pool{devs2, storage_pool::mode::truncate};
    }

    TEST(StoragePool, clone_content)
    {
        storage_pool pool1(use_anonymous_inode_tag{});
        storage_pool pool2(use_anonymous_inode_tag{});

        std::vector<std::byte> buffer1(1024 * 1024);
        memset(buffer1.data(), 0xee, buffer1.size());
        auto chunk1 = pool1.activate_chunk(storage_pool::seq, 0);
        {
            auto fd = chunk1->write_fd(buffer1.size());
            MONAD_ASSERT(
                -1 != ::pwrite(
                          fd.first,
                          buffer1.data(),
                          buffer1.size(),
                          static_cast<off_t>(fd.second)));
            EXPECT_EQ(chunk1->size(), buffer1.size());
        }
        std::vector<std::byte> buffer2(1024 * 1024);
        memset(buffer2.data(), 0xcc, buffer2.size());
        auto chunk2 = pool2.activate_chunk(storage_pool::seq, 0);
        {
            auto cloned = chunk1->clone_contents_into(*chunk2, UINT32_MAX);
            EXPECT_EQ(cloned, buffer1.size());
            auto fd = chunk2->read_fd();
            MONAD_ASSERT(
                -1 != ::pread(
                          fd.first,
                          buffer2.data(),
                          buffer2.size(),
                          static_cast<off_t>(fd.second)));
            EXPECT_EQ(chunk2->size(), buffer1.size());
        }
        EXPECT_EQ(0, memcmp(buffer1.data(), buffer2.data(), buffer1.size()));
    }
}
