#include <monad/core/address.hpp>
#include <monad/core/byte_string.hpp>

#include <monad/db/code_store.hpp>

#include <gtest/gtest.h>

#include <unordered_map>

using namespace monad;
using namespace monad::db;

static constexpr auto a = 0x5353535353535353535353535353535353535353_address;
static constexpr auto b = 0xbebebebebebebebebebebebebebebebebebebebe_address;
static constexpr auto c = 0xa5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5_address;
static constexpr auto c1 =
    byte_string{0x65, 0x74, 0x68, 0x65, 0x72, 0x6d, 0x69};
static constexpr auto c2 =
    byte_string{0x6e, 0x65, 0x20, 0x2d, 0x20, 0x45, 0x55, 0x31, 0x34};
static constexpr auto c3 =
    byte_string{0x6e, 0x63, 0x40, 0x2d, 0x20, 0x45, 0x55, 0x31, 0x33};

using db_t = std::unordered_map<address_t, byte_string>;

TEST(CodeStore, code_at)
{
    db_t db{};
    db.insert({a, c1});
    CodeStore s{db};

    auto const code = s.code_at(a);
    EXPECT_EQ(code, c1);
}

TEST(CodeStore, working_copy)
{
    db_t db{};
    db.insert({a, c1});
    CodeStore s{db};

    auto t = decltype(s)::WorkingCopy{s};
    auto const code_1 = t.code_at(a);
    EXPECT_EQ(code_1, c1);
}

TEST(CodeStoreWorkingCopy, set_code)
{
    db_t db{};
    db.insert({a, c1});
    CodeStore s{db};

    auto t = decltype(s)::WorkingCopy{s};
    t.set_code(b, c2);
    t.set_code(c, byte_string{});

    auto const code_1 = t.code_at(a);
    auto const code_2 = t.code_at(b);
    auto const code_3 = t.code_at(c);
    EXPECT_EQ(code_1, c1);
    EXPECT_EQ(code_2, c2);
    EXPECT_EQ(code_3, byte_string{});
}

TEST(CodeStoreWorkingCopy, get_code_size)
{
    db_t db{};
    db.insert({a, c1});
    CodeStore s{db};

    auto t = decltype(s)::WorkingCopy{s};
    auto const size = t.get_code_size(a);

    EXPECT_EQ(size, c1.size());
}

TEST(CodeStoreWorkingCopy, copy_code)
{
    db_t db{};
    db.insert({a, c1});
    db.insert({b, c2});
    CodeStore s{db};
    static constexpr unsigned size{8};
    uint8_t buffer[size];

    auto t = decltype(s)::WorkingCopy{s};

    { // underflow
        auto const total = t.copy_code(a, 0u, buffer, size);
        EXPECT_EQ(total, c1.size());
        EXPECT_EQ(0, std::memcmp(buffer, c1.c_str(), total));
    }
    { // offset
        static constexpr auto offset = 2u;
        static constexpr auto to_copy = 3u;
        auto const offset_total = t.copy_code(a, offset, buffer, to_copy);
        EXPECT_EQ(offset_total, to_copy);
        EXPECT_EQ(0, std::memcmp(buffer, c1.c_str() + offset, offset_total));
    }
    { // offset overflow
        static constexpr auto offset = 4u;
        auto const offset_total = t.copy_code(a, offset, buffer, size);
        EXPECT_EQ(offset_total, 3u);
        EXPECT_EQ(0, std::memcmp(buffer, c1.c_str() + offset, offset_total));
    }
    { // regular overflow
        auto const total = t.copy_code(b, 0u, buffer, size);
        EXPECT_EQ(total, size);
        EXPECT_EQ(0, std::memcmp(buffer, c2.c_str(), total));
    }
}

TEST(CodeStore, can_merge)
{
    db_t db{};
    db.insert({a, c1});
    CodeStore s{db};

    auto t = decltype(s)::WorkingCopy{s};
    t.set_code(b, c2);
    EXPECT_TRUE(s.can_merge(t));
}

TEST(CodeStore, merge_changes)
{
    db_t db{};
    db.insert({a, c1});
    CodeStore s{db};

    {
        auto t = decltype(s)::WorkingCopy{s};
        t.set_code(b, c2);
        EXPECT_TRUE(s.can_merge(t));
        s.merge_changes(t);
    }
    EXPECT_EQ(0, std::memcmp(s.code_at(b).c_str(), c2.c_str(), c2.size()));
}

TEST(CodeStore, revert)
{
    db_t db{};
    db.insert({a, c1});
    CodeStore s{db};

    {
        auto t = decltype(s)::WorkingCopy{s};
        t.set_code(b, c2);
        EXPECT_TRUE(s.can_merge(t));
        t.revert();
        s.merge_changes(t);
    }
    EXPECT_EQ(0, s.code_at(b).size());
}

TEST(CodeStore, cant_merge_colliding_merge)
{
    db_t db{};
    CodeStore s{db};

    {
        auto t = decltype(s)::WorkingCopy{s};
        t.set_code(a, c1);
        EXPECT_TRUE(s.can_merge(t));
        s.merge_changes(t);
    }
    {
        auto t = decltype(s)::WorkingCopy{s};
        t.set_code(a, c2);
        EXPECT_FALSE(s.can_merge(t));
    }
}

TEST(CodeStore, cant_merge_colliding_store)
{
    db_t db{};
    db.insert({a, c1});
    CodeStore s{db};

    auto t = decltype(s)::WorkingCopy{s};
    t.set_code(a, c2);
    EXPECT_FALSE(s.can_merge(t));
}

TEST(CodeStore, merge_multiple_changes)
{
    db_t db{};
    CodeStore s{db};

    {
        auto t = decltype(s)::WorkingCopy{s};
        t.set_code(a, c1);
        EXPECT_TRUE(s.can_merge(t));
        s.merge_changes(t);
    }
    {
        auto t = decltype(s)::WorkingCopy{s};
        t.set_code(b, c2);
        EXPECT_TRUE(s.can_merge(t));
        s.merge_changes(t);
    }
    EXPECT_EQ(0, std::memcmp(s.code_at(a).c_str(), c1.c_str(), c1.size()));
    EXPECT_EQ(0, std::memcmp(s.code_at(b).c_str(), c2.c_str(), c2.size()));
}

TEST(CodeStore, can_commit)
{
    db_t db{};
    db.insert({c, c3});
    CodeStore s{db};

    {
        auto t = decltype(s)::WorkingCopy{s};
        t.set_code(a, c1);
        t.set_code(b, c2);
        EXPECT_TRUE(s.can_merge(t));
        s.merge_changes(t);
    }
    EXPECT_TRUE(s.can_commit());
}

TEST(CodeStore, can_commit_multiple)
{
    db_t db{};
    CodeStore s{db};

    {
        auto t = decltype(s)::WorkingCopy{s};
        t.set_code(a, c1);
        t.set_code(b, c2);
        EXPECT_TRUE(s.can_merge(t));
        s.merge_changes(t);
    }
    EXPECT_TRUE(s.can_commit());
    s.commit_all_merged();
    {
        auto t = decltype(s)::WorkingCopy{s};
        t.set_code(c, c3);
        EXPECT_TRUE(s.can_merge(t));
        s.merge_changes(t);
    }
    EXPECT_TRUE(s.can_commit());
    s.commit_all_merged();

    EXPECT_EQ(0, std::memcmp(s.code_at(a).c_str(), c1.c_str(), c1.size()));
    EXPECT_EQ(0, std::memcmp(s.code_at(b).c_str(), c2.c_str(), c2.size()));
    EXPECT_EQ(0, std::memcmp(s.code_at(c).c_str(), c3.c_str(), c3.size()));
}
