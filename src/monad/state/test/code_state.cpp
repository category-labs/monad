#include <monad/core/address.hpp>
#include <monad/core/byte_string.hpp>

#include <monad/state/code_state.hpp>

#include <gtest/gtest.h>

#include <unordered_map>

using namespace monad;
using namespace monad::state;

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

TEST(CodeState, code_at)
{
    db_t db{};
    db.insert({a, c1});
    CodeState s{db};

    auto const code = s.code_at(a);
    EXPECT_EQ(code, c1);
}

TEST(CodeState, changeset)
{
    db_t db{};
    db.insert({a, c1});
    CodeState s{db};

    auto t = decltype(s)::ChangeSet{s};
    auto const code_1 = t.code_at(a);
    EXPECT_EQ(code_1, c1);
}

TEST(CodeStateChangeSet, set_code)
{
    db_t db{};
    db.insert({a, c1});
    CodeState s{db};

    auto t = decltype(s)::ChangeSet{s};
    t.set_code(b, c2);
    t.set_code(c, byte_string{});

    auto const code_1 = t.code_at(a);
    auto const code_2 = t.code_at(b);
    auto const code_3 = t.code_at(c);
    EXPECT_EQ(code_1, c1);
    EXPECT_EQ(code_2, c2);
    EXPECT_EQ(code_3, byte_string{});
}

TEST(CodeStateChangeSet, get_code_size)
{
    db_t db{};
    db.insert({a, c1});
    CodeState s{db};

    auto t = decltype(s)::ChangeSet{s};
    auto const size = t.get_code_size(a);

    EXPECT_EQ(size, c1.size());
}

TEST(CodeStateChangeSet, copy_code)
{
    db_t db{};
    db.insert({a, c1});
    db.insert({b, c2});
    CodeState s{db};
    static constexpr unsigned size{8};
    uint8_t buffer[size];

    auto t = decltype(s)::ChangeSet{s};

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

TEST(CodeState, can_merge)
{
    db_t db{};
    db.insert({a, c1});
    CodeState s{db};

    auto t = decltype(s)::ChangeSet{s};
    t.set_code(b, c2);
    EXPECT_TRUE(s.can_merge(t));
}

TEST(CodeState, merge_changes)
{
    db_t db{};
    db.insert({a, c1});
    CodeState s{db};

    {
        auto t = decltype(s)::ChangeSet{s};
        t.set_code(b, c2);
        EXPECT_TRUE(s.can_merge(t));
        s.merge_changes(t);
    }
    EXPECT_EQ(s.code_at(b), c2);
}

TEST(CodeState, revert)
{
    db_t db{};
    db.insert({a, c1});
    CodeState s{db};

    {
        auto t = decltype(s)::ChangeSet{s};
        t.set_code(b, c2);
        EXPECT_TRUE(s.can_merge(t));
        t.revert();
        s.merge_changes(t);
    }
    EXPECT_EQ(0, s.code_at(b).size());
}

TEST(CodeState, cant_merge_colliding_merge)
{
    db_t db{};
    CodeState s{db};

    {
        auto t = decltype(s)::ChangeSet{s};
        t.set_code(a, c1);
        EXPECT_TRUE(s.can_merge(t));
        s.merge_changes(t);
    }
    {
        auto t = decltype(s)::ChangeSet{s};
        t.set_code(a, c2);
        EXPECT_FALSE(s.can_merge(t));
    }
}

TEST(CodeState, cant_merge_colliding_store)
{
    db_t db{};
    db.insert({a, c1});
    CodeState s{db};

    auto t = decltype(s)::ChangeSet{s};
    t.set_code(a, c2);
    EXPECT_FALSE(s.can_merge(t));
}

TEST(CodeState, merge_multiple_changes)
{
    db_t db{};
    CodeState s{db};

    {
        auto t = decltype(s)::ChangeSet{s};
        t.set_code(a, c1);
        EXPECT_TRUE(s.can_merge(t));
        s.merge_changes(t);
    }
    {
        auto t = decltype(s)::ChangeSet{s};
        t.set_code(b, c2);
        EXPECT_TRUE(s.can_merge(t));
        s.merge_changes(t);
    }
    EXPECT_EQ(s.code_at(a), c1);
    EXPECT_EQ(s.code_at(b), c2);
}

TEST(CodeState, can_commit)
{
    db_t db{};
    db.insert({c, c3});
    CodeState s{db};

    {
        auto t = decltype(s)::ChangeSet{s};
        t.set_code(a, c1);
        t.set_code(b, c2);
        EXPECT_TRUE(s.can_merge(t));
        s.merge_changes(t);
    }
    EXPECT_TRUE(s.can_commit());
}

TEST(CodeState, can_commit_multiple)
{
    db_t db{};
    CodeState s{db};

    {
        auto t = decltype(s)::ChangeSet{s};
        t.set_code(a, c1);
        t.set_code(b, c2);
        EXPECT_TRUE(s.can_merge(t));
        s.merge_changes(t);
    }
    EXPECT_TRUE(s.can_commit());
    s.commit_all_merged();
    {
        auto t = decltype(s)::ChangeSet{s};
        t.set_code(c, c3);
        EXPECT_TRUE(s.can_merge(t));
        s.merge_changes(t);
    }
    EXPECT_TRUE(s.can_commit());
    s.commit_all_merged();

    EXPECT_EQ(s.code_at(a), c1);
    EXPECT_EQ(s.code_at(b), c2);
    EXPECT_EQ(s.code_at(c), c3);
}
