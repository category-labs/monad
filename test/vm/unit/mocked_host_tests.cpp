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

#include <category/core/address.hpp>
#include <category/core/bytes.hpp>
#include <category/vm/evm/storage_status.h>
#include <test/vm/utils/mocked_host.hpp>

#include <gtest/gtest.h>

using namespace monad;
using namespace monad::vm::test;

TEST(MockedHost, StorageStatus)
{
    struct Transition
    {
        bytes32_t original;
        bytes32_t current;
        bytes32_t value;
        monad_storage_status status;
    };

    auto const O = bytes32_t{};
    auto const X = bytes32_t{1};
    auto const Y = bytes32_t{2};
    auto const Z = bytes32_t{3};

    Transition const transitions[] = {
        {O, O, O, MONAD_STORAGE_ASSIGNED},
        {X, O, O, MONAD_STORAGE_ASSIGNED},
        {O, Y, Y, MONAD_STORAGE_ASSIGNED},
        {X, Y, Y, MONAD_STORAGE_ASSIGNED},
        {Y, Y, Y, MONAD_STORAGE_ASSIGNED},
        {O, Y, Z, MONAD_STORAGE_ASSIGNED},
        {X, Y, Z, MONAD_STORAGE_ASSIGNED},
        {O, O, Z, MONAD_STORAGE_ADDED},
        {X, X, O, MONAD_STORAGE_DELETED},
        {X, X, Z, MONAD_STORAGE_MODIFIED},
        {X, O, Z, MONAD_STORAGE_DELETED_ADDED},
        {X, Y, O, MONAD_STORAGE_MODIFIED_DELETED},
        {X, O, X, MONAD_STORAGE_DELETED_RESTORED},
        {O, Y, O, MONAD_STORAGE_ADDED_DELETED},
        {X, Y, X, MONAD_STORAGE_MODIFIED_RESTORED},
    };

    auto const addr = 0x00000000000000000000000000000000000000AA_address;
    auto const key = bytes32_t{7};

    for (auto const &t : transitions) {
        MockedHost host;
        host.accounts[addr].storage[key] = {
            .current = t.current, .original = t.original};
        EXPECT_EQ(host.set_storage(addr, key, t.value), t.status);
        EXPECT_EQ(host.get_storage(addr, key), t.value);
    }
}
