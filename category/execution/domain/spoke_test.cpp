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
#include <category/core/keccak.hpp>
#include <category/execution/domain/spoke.hpp>

#include <gtest/gtest.h>

using namespace monad;
using namespace monad::domain;
using namespace monad::literals;

TEST(DomainSpoke, code_is_what_the_constructor_deploys)
{
    // The hash of the code that deploying DomainSpoke with these constructor
    // arguments leaves, from `forge create` and `cast code` on anvil.
    EXPECT_EQ(
        to_bytes(keccak256(domain_spoke_code(
            5328559,
            20143,
            0x1111111111111111111111111111111111111111_address))),
        0xe20e6879acea2b66d9a59563941fa2c8e70a8bbdf8e5f51e2840c57008e52a3b_bytes32);
}

TEST(DomainSpoke, code_depends_on_each_argument)
{
    constexpr Address HUB{0x1111111111111111111111111111111111111111_address};
    auto const code = domain_spoke_code(5328559, 20143, HUB);
    EXPECT_NE(code, domain_spoke_code(5328560, 20143, HUB));
    EXPECT_NE(code, domain_spoke_code(5328559, 20144, HUB));
    EXPECT_NE(
        code,
        domain_spoke_code(
            5328559,
            20143,
            0x1111111111111111111111111111111111111112_address));
}
