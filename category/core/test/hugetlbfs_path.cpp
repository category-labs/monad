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

#include <cerrno>
#include <cstdio>
#include <print>

#include <gtest/gtest.h>
#include <unistd.h>

extern "C"
{
#include <hugetlbfs.h>
}

#include <category/core/mem/hugetlb_path.h>

TEST(HugetlbfsPath, Basic)
{
    int rc;
    int dirfd = -1;
    char hugetlbfs_path[2048];

    if (gethugepagesize() == -1) {
        // Huge pages aren't available; skip the test
        GTEST_SKIP();
    }

    monad_hugetlbfs_resolve_params params = {
        .page_size = 0, // Default huge page size
        .path_suffix = "hugetlb-path-test",
        .create_dirs = false,
        .dir_create_mode = 0775,
    };

    rc = monad_hugetlbfs_open_dir_fd(
        &params, &dirfd, hugetlbfs_path, sizeof hugetlbfs_path);
    if (rc == ENODEV) {
        // This host does not have a hugetlbfs we can write to
        // TODO(ken): we should make sure this is always supported in CI
        //   environments, and remove this skip
        GTEST_SKIP();
    }
    ASSERT_EQ(rc, ENOENT); // Can't create the suffix, and it doesn't exist
    ASSERT_EQ(dirfd, -1);
    std::println(
        stderr,
        "expected library error -- {}",
        monad_hugetlbfs_get_last_error());

    // Try again, this time we can create it
    params.create_dirs = true;
    rc = monad_hugetlbfs_open_dir_fd(
        &params, &dirfd, hugetlbfs_path, sizeof hugetlbfs_path);
    ASSERT_EQ(rc, 0);
    ASSERT_NE(dirfd, -1);
    std::println(stderr, "full path is: {}", hugetlbfs_path);
    ASSERT_EQ(hugetlbfs_test_path(hugetlbfs_path), 1);
    (void)close(dirfd);

    // Try again; we can't create it, but that's OK: it's there now
    params.create_dirs = false;
    rc = monad_hugetlbfs_open_dir_fd(
        &params, &dirfd, hugetlbfs_path, sizeof hugetlbfs_path);
    ASSERT_EQ(rc, 0);
    ASSERT_NE(dirfd, -1);
    ASSERT_EQ(hugetlbfs_test_path(hugetlbfs_path), 1);
    (void)close(dirfd);

    // Remove the file
    ASSERT_EQ(rmdir(hugetlbfs_path), 0);

    // Either parameter can be nullptr
    rc = monad_hugetlbfs_open_dir_fd(
        &params, nullptr, nullptr, sizeof hugetlbfs_path);
    ASSERT_EQ(rc, ENOENT);
}
