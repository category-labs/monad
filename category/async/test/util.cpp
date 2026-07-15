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

#include "gtest/gtest.h"

#include <category/async/config.hpp>
#include <category/async/util.hpp>

#include <filesystem>
#include <optional>
#include <stdexcept>
#include <string>

#include <linux/magic.h> // for TMPFS_MAGIC
#include <stdlib.h> // for setenv, mkdtemp, mkstemp
#include <sys/statfs.h> // for statfs
#include <unistd.h> // for unlink, close

namespace
{
    namespace fs = std::filesystem;
    using MONAD_ASYNC_NAMESPACE::detail::resolve_working_temporary_directory;

    constexpr char const *ENV = "MONAD_TMPDIR_FORCE";

    // Save and restore MONAD_TMPDIR_FORCE around each test so cases are
    // independent of one another and of the ambient environment.
    struct WorkingTempDir : public ::testing::Test
    {
        std::optional<std::string> saved;

        void SetUp() override
        {
            if (char const *const v = ::getenv(ENV); v != nullptr) {
                saved = v;
            }
            ::unsetenv(ENV);
        }

        void TearDown() override
        {
            if (saved.has_value()) {
                ::setenv(ENV, saved->c_str(), 1);
            }
            else {
                ::unsetenv(ENV);
            }
        }
    };

}

// Deliberately not covered here: the SUID/SGID gate in
// resolve_working_temporary_directory() (the override is honored only when
// getuid() == geteuid() && getgid() == getegid()) cannot be exercised without
// privileges, and an EACCES permission-denied directory is omitted because
// root -- which CI often runs as -- bypasses permission bits and would make
// mkstemp succeed, inverting the test.

// A forced directory is returned verbatim, bypassing the O_DIRECT probe.
TEST_F(WorkingTempDir, ForceHonoredForValidDirectory)
{
    std::string templ =
        (fs::temp_directory_path() / "monad_wtd_XXXXXX").native();
    char const *const p = ::mkdtemp(templ.data());
    ASSERT_NE(p, nullptr);
    fs::path const dir{p};
    ::setenv(ENV, dir.c_str(), 1);
    EXPECT_EQ(resolve_working_temporary_directory(), dir);
    fs::remove_all(dir);
}

// The forced location is honored even when it is a tmpfs, which the normal
// search deliberately rejects. This is the whole point of the override.
TEST_F(WorkingTempDir, ForceHonoredForTmpfs)
{
    fs::path const shm{"/dev/shm"};
    struct statfs s = {};
    if (::statfs(shm.c_str(), &s) != 0 || s.f_type != TMPFS_MAGIC) {
        GTEST_SKIP() << "/dev/shm is not a tmpfs on this host";
    }
    std::string templ = (shm / "monad_wtd_tmpfs_XXXXXX").native();
    char const *const p = ::mkdtemp(templ.data());
    ASSERT_NE(p, nullptr);
    fs::path const dir{p};
    ::setenv(ENV, dir.c_str(), 1);
    EXPECT_EQ(resolve_working_temporary_directory(), dir);
    fs::remove_all(dir);
}

// A set-but-nonexistent path throws rather than silently falling through.
TEST_F(WorkingTempDir, ForceThrowsForNonexistentPath)
{
    ::setenv(ENV, "/nonexistent/monad/tmpdir", 1);
    EXPECT_THROW(resolve_working_temporary_directory(), std::runtime_error);
}

// A path that exists but is a regular file (not a directory) throws.
TEST_F(WorkingTempDir, ForceThrowsForRegularFile)
{
    std::string templ =
        (fs::temp_directory_path() / "monad_wtd_file_XXXXXX").native();
    int const fd = ::mkstemp(templ.data());
    ASSERT_NE(fd, -1);
    ::close(fd);
    ::setenv(ENV, templ.c_str(), 1);
    EXPECT_THROW(resolve_working_temporary_directory(), std::runtime_error);
    ::unlink(templ.c_str());
}

// An empty value is treated as unset: the normal search runs and returns an
// existing directory.
TEST_F(WorkingTempDir, EmptyForceIsIgnored)
{
    ::setenv(ENV, "", 1);
    fs::path result;
    try {
        result = resolve_working_temporary_directory();
    }
    catch (std::runtime_error const &) {
        GTEST_SKIP() << "host has no O_DIRECT-capable temp dir";
    }
    EXPECT_TRUE(fs::is_directory(result)) << result;
}

// With the override unset, resolution still yields an existing directory.
TEST_F(WorkingTempDir, UnsetReturnsExistingDirectory)
{
    fs::path result;
    try {
        result = resolve_working_temporary_directory();
    }
    catch (std::runtime_error const &) {
        GTEST_SKIP() << "host has no O_DIRECT-capable temp dir";
    }
    EXPECT_TRUE(fs::is_directory(result)) << result;
}
