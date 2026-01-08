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

#include <category/core/fiber/fiber_write.hpp>
#include <category/core/fiber/uring_write_scheduler.hpp>

#include <category/core/test_util/gtest_signal_stacktrace_printer.hpp> // NOLINT

#include <gtest/gtest.h>

#include <liburing.h>

#include <cstdio>
#include <fcntl.h>
#include <filesystem>
#include <sys/stat.h>
#include <unistd.h>

using namespace monad::fiber;

class UringFiberSchedulerTest : public ::testing::Test
{
protected:
    io_uring ring_{};
    std::filesystem::path temp_file_;
    int fd_{-1};

    void SetUp() override
    {
        // Initialize io_uring with a small queue
        int ret = io_uring_queue_init(32, &ring_, 0);
        ASSERT_EQ(ret, 0) << "Failed to init io_uring: " << strerror(-ret);

        // Create temp file for write tests
        temp_file_ = std::filesystem::temp_directory_path() / "uring_fiber_test.tmp";
        fd_ = open(temp_file_.c_str(), O_CREAT | O_RDWR | O_TRUNC, 0644);
        ASSERT_GE(fd_, 0) << "Failed to create temp file: " << strerror(errno);
    }

    void TearDown() override
    {
        if (fd_ >= 0) {
            close(fd_);
        }
        if (!temp_file_.empty()) {
            std::filesystem::remove(temp_file_);
        }
        io_uring_queue_exit(&ring_);
    }

    // Helper to do a synchronous write using io_uring directly
    // (validates io_uring is working without fiber involvement)
    ssize_t sync_uring_write(
        std::span<std::byte const> buffer, uint64_t offset)
    {
        io_uring_sqe* sqe = io_uring_get_sqe(&ring_);
        EXPECT_NE(sqe, nullptr);
        if (!sqe) return -1;

        io_uring_prep_write(sqe, fd_, buffer.data(),
            static_cast<unsigned>(buffer.size()), offset);
        io_uring_sqe_set_data(sqe, nullptr);

        int ret = io_uring_submit(&ring_);
        EXPECT_GT(ret, 0);
        if (ret <= 0) return -1;

        io_uring_cqe* cqe = nullptr;
        ret = io_uring_wait_cqe(&ring_, &cqe);
        EXPECT_EQ(ret, 0);
        if (ret != 0) return -1;

        ssize_t result = cqe->res;
        io_uring_cqe_seen(&ring_, cqe);
        return result;
    }
};

// Test basic io_uring write (no fibers, validates test setup)
TEST_F(UringFiberSchedulerTest, sync_write)
{
    std::array<std::byte, 4096> buffer{};
    std::fill(buffer.begin(), buffer.end(), std::byte{0x42});

    ssize_t written = sync_uring_write(
        std::span<std::byte const>(buffer), 0);
    EXPECT_EQ(written, 4096);

    // Verify file contents
    std::array<std::byte, 4096> verify_buffer{};
    lseek(fd_, 0, SEEK_SET);
    ssize_t bytes_read = read(fd_, verify_buffer.data(), verify_buffer.size());
    EXPECT_EQ(bytes_read, 4096);
    for (auto b : verify_buffer) {
        EXPECT_EQ(b, std::byte{0x42});
    }
}

// Test CompletionToken structure
TEST_F(UringFiberSchedulerTest, completion_token)
{
    CompletionToken token;
    EXPECT_EQ(token.magic, CompletionToken::FIBER_COMPLETION_MAGIC);
    EXPECT_EQ(token.waiting_fiber, nullptr);
    EXPECT_EQ(token.result, 0);
    EXPECT_FALSE(token.completed);

    // Simulate completion
    token.result = 4096;
    token.completed = true;
    EXPECT_EQ(token.result, 4096);
    EXPECT_TRUE(token.completed);
}

// Test WriteResult structure
TEST_F(UringFiberSchedulerTest, write_result)
{
    WriteResult success_result{4096, true};
    EXPECT_TRUE(success_result);
    EXPECT_EQ(success_result.bytes_written, 4096);
    EXPECT_TRUE(success_result.success);

    WriteResult failure_result{-1, false};
    EXPECT_FALSE(failure_result);
    EXPECT_EQ(failure_result.bytes_written, -1);
    EXPECT_FALSE(failure_result.success);
}

// Test multiple sequential sync writes
TEST_F(UringFiberSchedulerTest, sequential_sync_writes)
{
    constexpr size_t num_writes = 10;
    constexpr size_t write_size = 1024;

    for (size_t i = 0; i < num_writes; ++i) {
        std::array<std::byte, write_size> buffer{};
        std::fill(buffer.begin(), buffer.end(), static_cast<std::byte>(i));

        ssize_t written = sync_uring_write(
            std::span<std::byte const>(buffer), i * write_size);
        EXPECT_EQ(written, static_cast<ssize_t>(write_size));
    }

    // Verify file size
    struct stat st{};
    fstat(fd_, &st);
    EXPECT_EQ(st.st_size, static_cast<off_t>(num_writes * write_size));

    // Verify each region
    for (size_t i = 0; i < num_writes; ++i) {
        std::array<std::byte, write_size> verify_buffer{};
        lseek(fd_, static_cast<off_t>(i * write_size), SEEK_SET);
        ssize_t bytes_read = read(fd_, verify_buffer.data(), verify_buffer.size());
        EXPECT_EQ(bytes_read, static_cast<ssize_t>(write_size));
        for (auto b : verify_buffer) {
            EXPECT_EQ(b, static_cast<std::byte>(i));
        }
    }
}
