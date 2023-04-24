#include <monad/core/account.hpp>
#include <monad/core/address.hpp>
#include <monad/core/bytes.hpp>

#include <monad/db/datum.hpp>

#include <gtest/gtest.h>

#include <unordered_map>
#include <unordered_set>

using namespace monad;
using namespace monad::db;

TEST(diff, bytes32_unordered_map)
{
    static constexpr auto a =
        0xbebebebebebebebebebebebebebebebebebebebe_address;
    static constexpr auto b =
        0xEA674fdDe714fd979de3EdF0F56AA9716B898ec8_address;
    static constexpr auto key1 =
        0x00000000000000000000000000000000000000000000000000000000cafebabe_bytes32;
    static constexpr auto key2 =
        0x1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c_bytes32;
    static constexpr auto null =
        0x0000000000000000000000000000000000000000000000000000000000000000_bytes32;

    std::unordered_map<address_t, diff<bytes32_t>> m{};
    m[a] = key1;

    EXPECT_EQ(m[a].orig, null);
    EXPECT_EQ(m[a].updated, key1);

    m.insert({b, diff<bytes32_t>{key1, key2}});
    EXPECT_EQ(m[b].orig, key1);
    EXPECT_EQ(m[b].updated, key2);
}

TEST(diff, optional_account_unordered_map)
{
    static constexpr auto a =
        0xbebebebebebebebebebebebebebebebebebebebe_address;
    static constexpr auto b =
        0xEA674fdDe714fd979de3EdF0F56AA9716B898ec8_address;
    static constexpr auto hash1 =
        0x00000000000000000000000000000000000000000000000000000000cafebabe_bytes32;
    static constexpr auto hash2 =
        0x1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c_bytes32;
    static constexpr Account a1{
        .balance = 10'000'000'000u,
        .code_hash = hash1,
        .nonce = 11,
    };
    static constexpr Account a2{
        .balance = 20'000'000'000u,
        .code_hash = hash2,
        .nonce = 0,
    };
    std::unordered_map<address_t, diff<std::optional<Account>>> m{};
    m[a] = a1;

    EXPECT_FALSE(m[a].orig.has_value());
    EXPECT_EQ(m[a].updated, a1);

    m.insert({b, {a1, a2}});
    EXPECT_EQ(*m[b].orig, a1);
    EXPECT_EQ(m[b].updated, a2);
}

TEST(deleted_key, unordered_set)
{
    static constexpr auto a =
        0xbebebebebebebebebebebebebebebebebebebebe_address;
    static constexpr auto key1 =
        0x00000000000000000000000000000000000000000000000000000000cafebabe_bytes32;
    static constexpr auto key2 =
        0x1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c_bytes32;

    std::unordered_map<
        address_t,
        std::unordered_set<
            deleted_key,
            deleted_key::hash,
            deleted_key::equality>>
        m{};
    m[a].insert(deleted_key{key1, key2});
    m[a].insert(deleted_key{key2, key2});

    EXPECT_EQ(std::size(m[a]), 1u);
    auto const i = m[a].find(deleted_key{{}, key1});
    EXPECT_EQ(i, std::cend(m[a]));

    m[a].insert({key1, key1});

    EXPECT_EQ(std::size(m[a]), 2u);

    m[a].insert({key2, key1});

    EXPECT_EQ(std::size(m[a]), 2u);

    EXPECT_EQ(*m[a].find(deleted_key{key1}), key1);
}
