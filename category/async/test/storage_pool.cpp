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
#include <category/async/util.hpp>
#include <category/core/assert.h>
#include <category/core/test_util/gtest_signal_stacktrace_printer.hpp> // NOLINT
#include <category/core/test_util/temp_file_cleanup.hpp>

#include <cstddef>
#include <cstdint>
#include <cstring>
#include <filesystem>
#include <iostream>
#include <stdio.h>
#include <vector>

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
        // smallest a pool can be -- the conventional chunks plus one -- to
        // keep what this writes to 64 Mb.
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
        ASSERT_DEATH(
            (storage_pool{copy, storage_pool::mode::open_existing, flags}),
            "was initialised with a configuration different to this storage "
            "pool");
        storage_pool{copy, storage_pool::mode::truncate, flags};
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
