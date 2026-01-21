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

/**
 * @file
 *
 * This file tests execution event SDK functions that are not otherwise
 * tested by event_recorder.cpp.
 *
 * The only way to test the reader and writer is to test them together, so
 * the basic tests of the iterator correctness are in event_recorder.cpp. This
 * file tests "extra" reader-only SDK functionality like the snapshot API.
 */

#include <category/core/event/event_ring.h>
#include <category/core/event/event_ring_util.h>

#include <filesystem>

#include <errno.h>
#include <fcntl.h>
#include <sys/mman.h>
#include <unistd.h>

#include <gtest/gtest.h>

namespace fs = std::filesystem;

TEST(EventSnapshotTest, IsSnapshot)
{
    bool is_snapshot;
    fs::path const snapshot_file =
        fs::path{TEST_DATA_DIR} / "data" / "event" / "emn-1b-15m.snapshot";
    int fd = open(snapshot_file.c_str(), O_RDONLY);
    ASSERT_NE(fd, -1);
    ASSERT_EQ(
        0,
        monad_event_is_snapshot_file(fd, snapshot_file.c_str(), &is_snapshot));
    EXPECT_TRUE(is_snapshot);
    close(fd);

    fd = open("/etc/passwd", O_RDONLY);
    ASSERT_NE(fd, -1);
    ASSERT_EQ(0, monad_event_is_snapshot_file(fd, "/etc/passwd", &is_snapshot));
    EXPECT_FALSE(is_snapshot);
    close(fd);
}

TEST(EventSnapshotTest, Decompress)
{
    fs::path const snapshot_file =
        fs::path{TEST_DATA_DIR} / "data" / "event" / "emn-1b-15m.snapshot";
    int fd_in = open(snapshot_file.c_str(), O_RDONLY);
    int fd_out;
    ASSERT_NE(fd_in, -1);
    ASSERT_EQ(
        0,
        monad_event_decompress_snapshot_fd(
            fd_in, MONAD_EVENT_NO_MAX_SIZE, snapshot_file.c_str(), &fd_out));

    // When the above succeeds, decompressed fd_out contents must be mmap-able
    // as if it were a normal event ring file
    monad_event_ring ring;
    ASSERT_EQ(
        0,
        monad_event_ring_mmap(
            &ring, PROT_READ, 0, fd_out, 0, snapshot_file.c_str()));
    monad_event_ring_unmap(&ring);
    close(fd_out);

    // Decompressed size exceeds max size of 1024; this should return ENOBUFS
    ASSERT_EQ(
        ENOBUFS,
        monad_event_decompress_snapshot_fd(
            fd_in, 1024, snapshot_file.c_str(), &fd_out));

    // Open a non-snapshot file, check that decompression returns EPROTO
    // (our conventional "wrong format" error code)
    close(fd_in);
    fd_in = open("/etc/passwd", O_RDONLY);
    ASSERT_EQ(
        EPROTO,
        monad_event_decompress_snapshot_fd(
            fd_in, MONAD_EVENT_NO_MAX_SIZE, "/etc/passwd", &fd_out));
    ASSERT_EQ(-1, fd_out);
    close(fd_in);
}
