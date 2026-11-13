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

#include <category/core/byte_string.hpp>
#include <category/core/bytes.hpp>
#include <category/core/hex.hpp>
#include <category/core/keccak.hpp>

#include <monad/test/contract.hpp>

#include <gtest/gtest.h>

using namespace monad;
using namespace monad::test;

TEST(Contract, derives_hash_and_intercode)
{
    auto const code = from_hex("600060000160005500").value();
    Contract const contract{code};

    EXPECT_EQ(contract.code, code);
    EXPECT_EQ(contract.hash, to_bytes(keccak256(code)));
    ASSERT_NE(contract.icode, nullptr);
    EXPECT_EQ(
        byte_string_view(contract.icode->code(), contract.icode->size()),
        byte_string_view{code});
}

TEST(Contract, empty_code)
{
    Contract const contract{byte_string_view{}};

    EXPECT_TRUE(contract.code.empty());
    EXPECT_EQ(contract.hash, NULL_HASH);
    ASSERT_NE(contract.icode, nullptr);
    EXPECT_EQ(contract.icode->size(), 0u);
}
