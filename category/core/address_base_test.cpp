// Copyright (C) 2026 Category Labs, Inc.
//
// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with this program. If not, see <http://www.gnu.org/licenses/>.

#include <category/core/address.hpp>

#include <evmc/evmc.hpp>
#include <gtest/gtest.h>

#include <type_traits>

using namespace monad;

TEST(AddressBase, borrows_real_evmc_and_monad_objects)
{
    evmc_address raw{};
    evmc::address wrapped{};
    Address owned{};
    EXPECT_EQ(static_cast<evmc_address const &>(raw).bytes, raw.bytes);
    EXPECT_EQ(static_cast<evmc_address const &>(wrapped).bytes, wrapped.bytes);
    EXPECT_EQ(static_cast<evmc_address const &>(owned).bytes, owned.bytes);

    evmc_address const &view = raw;
    raw.bytes[19] = 42;
    EXPECT_EQ(view.bytes[19], 42);
}

TEST(AddressBase, owned_copy_does_not_borrow)
{
    evmc_address raw{};
    raw.bytes[0] = 3;
    Address copy{raw};
    raw.bytes[0] = 9;
    EXPECT_EQ(copy.bytes[0], 3);
    EXPECT_FALSE(address_equal(copy, raw));
}

TEST(AddressBase, equality_and_hash_match_owned_addresses)
{
    for (unsigned i = 0; i < 20; ++i) {
        evmc_address raw{};
        raw.bytes[i] = 0xab;
        Address const owned{raw};
        evmc_address const &view = raw;
        EXPECT_TRUE(address_equal(view, owned));
        EXPECT_TRUE(address_equal(owned, view));
        EXPECT_EQ(std::hash<Address>{}(view), std::hash<Address>{}(owned));
        EXPECT_EQ(
            ankerl::unordered_dense::hash<Address>{}(view),
            ankerl::unordered_dense::hash<Address>{}(owned));
        EXPECT_FALSE(address_equal(view, Address{}));
    }
}

TEST(AddressBase, constexpr_comparison_and_copy)
{
    static constexpr evmc_address raw{{1, 2, 3}};
    static constexpr evmc_address const &view = raw;
    static constexpr Address owned{view};
    static_assert(address_equal(view, owned));
    static_assert(!is_zero(view));
    EXPECT_TRUE(address_equal(view, owned));
}

TEST(AddressBase, heterogeneous_lookup_and_owned_insertion)
{
    using Map = ankerl::unordered_dense::segmented_map<
        Address,
        int,
        ankerl::unordered_dense::hash<Address>,
        AddressEqual>;
    Map map;
    evmc_address raw{};
    raw.bytes[19] = 7;
    evmc_address const &view = raw;

    EXPECT_EQ(map.find(view), map.end());
    auto const [it, inserted] = map.try_emplace(view, 42);
    EXPECT_TRUE(inserted);
    EXPECT_EQ(map.find(view), it);
    EXPECT_EQ(map.find(Address{7}), it);
    EXPECT_FALSE(map.try_emplace(view, 99).second);
    EXPECT_EQ(map.find(view)->second, 42);

    // The table owns its key even though insertion received a borrowed view.
    raw.bytes[19] = 8;
    EXPECT_EQ(map.find(view), map.end());
    EXPECT_EQ(map.find(Address{7})->second, 42);
}
