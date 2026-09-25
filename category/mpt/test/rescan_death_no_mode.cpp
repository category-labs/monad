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

#include "rescan_devices_test_util.hpp"

#include <category/async/config.hpp>
#include <category/async/detail/scope_polyfill.hpp>
#include <category/async/storage_pool.hpp>
#include <category/core/assert.h>
#include <category/core/log.hpp>

#include <gtest/gtest.h>

#include <csignal>
#include <cstring>
#include <filesystem>
#include <iostream>

#include <unistd.h>

using namespace MONAD_ASYNC_NAMESPACE;
using rescan_test::BLKSIZE;
using rescan_test::create_temp_file;
using rescan_test::extend_in_place;
using rescan_test::opened_db;
using rescan_test::rescan_flags;

namespace
{
    // This test's designed outcome is an abort, so a scope guard would never
    // run and the fixture -- half a gigabyte of real blocks once the pool is
    // created -- would be left behind on every run.
    char fixture_path[4096];

    extern "C" void unlink_fixture_then_die(int const sig)
    {
        if (fixture_path[0] != '\0') {
            (void)::unlink(fixture_path);
        }
        (void)::signal(sig, SIG_DFL);
        (void)::raise(sig);
    }
}

// A pool grown at the storage layer but opened without mode::rescan must
// abort telling the operator to run monad-mpt --rescan-devices. Its own
// executable because it aborts while holding io_uring rings, which in-process
// death tests handle poorly.
TEST(rescan_death, growth_refused_without_rescan_mode)
{
    monad::start_logger_minimal();

    auto const dev0 = create_temp_file(20 * BLKSIZE);
    auto const undev = monad::make_scope_exit(
        [&]() noexcept { std::filesystem::remove(dev0); });
    MONAD_ASSERT(dev0.native().size() < sizeof(fixture_path));
    std::strncpy(fixture_path, dev0.c_str(), sizeof(fixture_path) - 1);
    (void)::signal(SIGABRT, unlink_fixture_then_die);
    file_offset_t recorded = 0;
    {
        opened_db const db{dev0, storage_pool::mode::create_if_needed};
        recorded = db.aux.metadata_ctx().main()->recorded_device_size;
    }
    extend_in_place(dev0, 30 * BLKSIZE + 16384);
    {
        // The pool takes up the new space, but only monad-mpt's own
        // mode::rescan open is allowed to grow the database's chunk_info[].
        storage_pool const pool{
            dev0, storage_pool::mode::rescan, rescan_flags(recorded)};
    }
    std::cout << "Must fail after this:" << std::endl;
    opened_db const db{dev0, storage_pool::mode::open_existing};
}
