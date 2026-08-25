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

#include "add_devices_test_util.hpp"

#include <category/async/config.hpp>
#include <category/async/detail/scope_polyfill.hpp>
#include <category/async/storage_pool.hpp>
#include <category/core/log.hpp>

#include <gtest/gtest.h>

#include <filesystem>
#include <iostream>

using namespace MONAD_ASYNC_NAMESPACE;
using add_devices_test::BLKSIZE;
using add_devices_test::create_temp_file;
using add_devices_test::opened_db;

// A pool grown at the storage layer but opened without mode::add_devices must
// abort telling the operator to run monad-mpt --rescan-devices. Its own
// executable because it aborts while holding io_uring rings, which in-process
// death tests handle poorly.
TEST(add_devices_death, growth_refused_without_add_devices_mode)
{
    monad::start_logger_minimal();

    auto const dev0 = create_temp_file(20 * BLKSIZE);
    auto const dev1 = create_temp_file(10 * BLKSIZE);
    auto const undevs = monad::make_scope_exit([&]() noexcept {
        std::filesystem::remove(dev0);
        std::filesystem::remove(dev1);
    });
    std::filesystem::path const one[] = {dev0};
    std::filesystem::path const both[] = {dev0, dev1};
    {
        opened_db const db{one, storage_pool::mode::create_if_needed};
    }
    {
        storage_pool const pool{both, storage_pool::mode::add_devices};
    }
    std::cout << "Must fail after this:" << std::endl;
    opened_db const db{both, storage_pool::mode::open_existing};
}
