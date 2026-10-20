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

#include "test_fixtures_base.hpp"

#include <category/core/assert.h>
#include <category/core/byte_string.hpp>
#include <category/core/bytes.hpp>
#include <category/mpt/db.hpp>
#include <category/mpt/detail/timeline.hpp>
#include <category/mpt/lbt/compute.hpp>
#include <category/mpt/lbt/key_path.hpp>
#include <category/mpt/nibbles_view.hpp>
#include <category/mpt/node.hpp>
#include <category/mpt/node_cursor.hpp>
#include <category/mpt/state_machine.hpp>
#include <category/mpt/test/lbt_test_support.hpp>
#include <category/mpt/trie.hpp>
#include <category/mpt/update.hpp>

#include <gtest/gtest.h>

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <map>
#include <memory>
#include <optional>
#include <random>
#include <utility>
#include <vector>

using namespace monad;
using namespace monad::literals;
using namespace monad::mpt;
using namespace monad::test;

namespace
{
    // A change to any of these is a change of state commitment.
    constexpr bytes32_t PIN_SINGLE_AND_TWO_KEYS{
        0xf4e1ab21c4693fa3c429129b2dce27a515794ca628979a1753b40cfa6b148b38_bytes32};
    constexpr bytes32_t PIN_RANDOM_BATCHES{
        0x964b978e8e4b6b1c5c52250babe40a3f1cec10c0e3c1f66398df18bb32bc3667_bytes32};
    constexpr bytes32_t PIN_LONG_SHARED_PREFIX{
        0x97276414f6eba0e732de08195b82c8b1b0365691b6d26749c79d075d90059466_bytes32};
    constexpr bytes32_t PIN_ERASE_LEAVES_LONE_BRANCH_CHILD{
        0x917eac05679c0cac9d4046fa1efeca205079b944bf02b63283521a10ff6f61b1_bytes32};
    constexpr bytes32_t PIN_ERASE_TO_SINGLE_KEY{
        0xa045ae0191de3a5a423803cfdaa48f3e439b9a6d36d7d404e7eb9a7efcd88dcb_bytes32};
    constexpr bytes32_t PIN_ERASE_ALL_THEN_REINSERT{
        0x64fb7fb2d5d2a6bf366ba9d0981a778d7022501de8101095bd846815cf736418_bytes32};
    constexpr bytes32_t PIN_BINDS_BITS_ABOVE_ATTACH_POINT{
        0xd10feae360bcbbaef8ea716220348b99e94726e4f2b71c97c91b30f54c97133b_bytes32};
    constexpr bytes32_t PIN_ERASE_LIFTS_LEAF_FROM_DISK{
        0xcb16ad60cd2f155fcefba000fdb193abb770bfe9c06e14015ad6b24d1b9c273e_bytes32};
    constexpr bytes32_t PIN_ERASE_LIFTS_LEAF_ACROSS_LEVELS{
        0xe7b89749031d8ee14bc773cf067bbdfc48b221f01262cffb33b0bfeba9325ad0_bytes32};
    constexpr bytes32_t PIN_DB_ROOT_200_KEYS{
        0xfece661d718bbd070bc9eeec2674ee4a3c79ad4926edb015023a6774f58f2c8f_bytes32};

    byte_string_view key_view(bytes32_t const &k)
    {
        return byte_string_view{k.bytes, sizeof(k.bytes)};
    }

    // StateMachineAlways plus the key path that full-key leaves need.
    template <size_t CacheDepth>
    class KeyedMachine final : public StateMachine
    {
        size_t depth_{0};
        lbt::KeyPath path_;

    public:
        virtual std::unique_ptr<StateMachine> clone() const override
        {
            return std::make_unique<KeyedMachine>(*this);
        }

        virtual void down(unsigned char const nibble) override
        {
            path_.set(static_cast<unsigned>(depth_), nibble);
            ++depth_;
        }

        virtual void down(NibblesView const path) override
        {
            path_.set(static_cast<unsigned>(depth_), path);
            depth_ += path.nibble_size();
        }

        virtual void up(size_t const n) override
        {
            MONAD_ASSERT(n <= depth_);
            depth_ -= n;
        }

        // Depth 0 is the trie root, which no parent hashes: a Db keeps the
        // commitment in its root's data, and a raw trie's caller computes it.
        virtual Compute &get_compute() const override
        {
            static lbt::LbtDataCompute root;
            static lbt::LbtCompute<RawValueHasher> node;
            if (depth_ == 0) {
                return root;
            }
            node.bind_key(path_.view(0, static_cast<unsigned>(depth_)));
            return node;
        }

        virtual bool cache() const override
        {
            return depth_ < CacheDepth;
        }

        virtual bool compact() const override
        {
            return true;
        }

        virtual bool is_variable_length() const override
        {
            return false;
        }
    };

    template <class Base>
    struct LbtFixture : public Base
    {
        KeyedMachine<2> sm;
        ReferenceTrie ref;
        uint64_t version{0};
        std::map<bytes32_t, byte_string> live;

        struct Op
        {
            bytes32_t key;
            std::optional<byte_string> value; // nullopt = erase
        };

        void apply(std::vector<Op> const &ops)
        {
            std::vector<Update> updates;
            updates.reserve(ops.size());
            for (auto const &op : ops) {
                if (op.value) {
                    updates.push_back(make_update(key_view(op.key), *op.value));
                    ref.upsert(op.key, leaf_value(*op.value));
                    live[op.key] = *op.value;
                }
                else {
                    updates.push_back(make_erase(key_view(op.key)));
                    ref.erase(op.key);
                    live.erase(op.key);
                }
            }
            this->root = upsert_vector(
                this->aux,
                sm,
                std::move(this->root),
                std::move(updates),
                version);
            // An empty trie writes no root, so the on-disk db does not record
            // this version and the next write must reuse it.
            if (this->root) {
                ++version;
            }
            expect_all_live_keys_read_back();
        }

        void expect_all_live_keys_read_back()
        {
            if (live.empty()) {
                return;
            }
            uint64_t const v = version - 1;
            // find_blocking attaches the nodes it reads, so on disk it runs
            // on a separate root and leaves the engine's trie untouched.
            Node::SharedPtr disk_root;
            if (this->aux.is_on_disk()) {
                disk_root = read_node_blocking(
                    this->aux,
                    this->aux.metadata_ctx().get_root_offset_at_version(
                        v, timeline_id::primary),
                    v,
                    timeline_id::primary);
                ASSERT_NE(disk_root, nullptr);
            }
            NodeCursor const start{disk_root ? disk_root : this->root};
            for (auto const &[k, val] : live) {
                auto const [cursor, res] = find_blocking(
                    this->aux,
                    start,
                    NibblesView{key_view(k)},
                    v,
                    timeline_id::primary);
                ASSERT_EQ(res, find_result::success);
                EXPECT_EQ(cursor.node->value(), byte_string_view{val});
            }
        }

        bytes32_t engine_root() const
        {
            return trie_root(this->root.get());
        }

        void expect_equal_roots()
        {
            EXPECT_EQ(engine_root(), ref.root());
        }

        void expect_pinned_root(bytes32_t const &pin)
        {
            expect_equal_roots();
            EXPECT_EQ(ref.root(), pin);
        }
    };

    bytes32_t random_key(std::mt19937_64 &rng)
    {
        bytes32_t k;
        for (auto &b : k.bytes) {
            b = static_cast<uint8_t>(rng());
        }
        return k;
    }

    byte_string value_of(uint64_t const x)
    {
        return byte_string(32, static_cast<unsigned char>(x & 0xff)) +
               byte_string(1, static_cast<unsigned char>(x >> 8));
    }
}

template <typename F>
struct LbtOracleTest : public F
{
};

using LbtFixtures = ::testing::Types<
    LbtFixture<InMemoryTrieBase<::testing::Test>>,
    LbtFixture<OnDiskTrieBase<::testing::Test>>>;
TYPED_TEST_SUITE(LbtOracleTest, LbtFixtures);

TYPED_TEST(LbtOracleTest, single_and_two_keys)
{
    std::mt19937_64 rng{1};
    auto const a = random_key(rng);
    auto const b = random_key(rng);
    this->apply({{a, value_of(1)}});
    this->expect_equal_roots();
    this->apply({{b, value_of(2)}});
    this->expect_pinned_root(PIN_SINGLE_AND_TWO_KEYS);
}

TYPED_TEST(LbtOracleTest, random_batches)
{
    // Each batch touches disjoint keys: updates and erases are drawn from the
    // keys live before the batch, inserts are fresh.
    std::mt19937_64 rng{2};
    std::vector<bytes32_t> live;
    for (int batch = 0; batch < 20; ++batch) {
        std::ranges::shuffle(live, rng);
        size_t const n_update = std::min<size_t>(live.size(), 15);
        size_t const n_erase = std::min<size_t>(live.size() - n_update, 10);
        std::vector<typename TypeParam::Op> ops;
        ops.reserve(n_update + n_erase + 25);
        for (size_t i = 0; i < n_update; ++i) {
            ops.push_back({live[i], value_of(rng())});
        }
        for (size_t i = n_update; i < n_update + n_erase; ++i) {
            ops.push_back({live[i], std::nullopt});
        }
        auto const erased = live.begin() + static_cast<ptrdiff_t>(n_update);
        live.erase(erased, erased + static_cast<ptrdiff_t>(n_erase));
        for (int i = 0; i < 25; ++i) {
            auto const k = random_key(rng);
            ops.push_back({k, value_of(rng())});
            live.push_back(k);
        }
        this->apply(ops);
        this->expect_equal_roots();
    }
    this->expect_pinned_root(PIN_RANDOM_BATCHES);
}

TYPED_TEST(LbtOracleTest, long_shared_prefix)
{
    bytes32_t a{};
    for (auto &byte : a.bytes) {
        byte = 0x77;
    }
    bytes32_t b = a;
    b.bytes[31] = 0x78;
    bytes32_t c = a;
    c.bytes[31] = 0x87;
    this->apply({{a, value_of(1)}, {b, value_of(2)}});
    this->expect_equal_roots();
    this->apply({{c, value_of(3)}});
    this->expect_pinned_root(PIN_LONG_SHARED_PREFIX);
}

TYPED_TEST(LbtOracleTest, erase_leaves_lone_branch_child)
{
    bytes32_t a{};
    a.bytes[0] = 0x56;
    a.bytes[1] = 0x71;
    bytes32_t b{};
    b.bytes[0] = 0x56;
    b.bytes[1] = 0x72;
    bytes32_t c{};
    c.bytes[0] = 0x59;
    this->apply({{a, value_of(1)}, {b, value_of(2)}, {c, value_of(3)}});
    this->expect_equal_roots();
    this->apply({{c, std::nullopt}});
    this->expect_pinned_root(PIN_ERASE_LEAVES_LONE_BRANCH_CHILD);
}

TYPED_TEST(LbtOracleTest, erase_to_single_key)
{
    std::mt19937_64 rng{3};
    std::vector<bytes32_t> keys;
    std::vector<typename TypeParam::Op> ops;
    for (int i = 0; i < 40; ++i) {
        keys.push_back(random_key(rng));
        ops.push_back({keys.back(), value_of(static_cast<uint64_t>(i))});
    }
    this->apply(ops);
    std::vector<typename TypeParam::Op> erase_ops;
    for (size_t i = 1; i < keys.size(); ++i) {
        erase_ops.push_back({keys[i], std::nullopt});
    }
    this->apply(erase_ops);
    this->expect_pinned_root(PIN_ERASE_TO_SINGLE_KEY);
}

TYPED_TEST(LbtOracleTest, full_fanout)
{
    // One key per value of the first nibble: the root node has 16 children.
    auto const keys = [] {
        std::vector<bytes32_t> out;
        out.reserve(16);
        for (unsigned u = 0; u < 16; ++u) {
            bytes32_t k{};
            k.bytes[0] = static_cast<uint8_t>(u << 4);
            k.bytes[31] = static_cast<uint8_t>(u);
            out.push_back(k);
        }
        return out;
    }();
    std::vector<typename TypeParam::Op> ops;
    ops.reserve(16);
    for (unsigned u = 0; u < 16; ++u) {
        ops.push_back({keys[u], value_of(u)});
    }
    this->apply(ops);
    this->expect_equal_roots();
    EXPECT_EQ(this->root->number_of_children(), 16u);

    ops.clear();
    for (unsigned u = 0; u < 16; ++u) {
        ops.push_back({keys[u], value_of(u + 1000)});
    }
    this->apply(ops);
    this->expect_equal_roots();
    EXPECT_EQ(this->root->number_of_children(), 16u);
}

TYPED_TEST(LbtOracleTest, keys_differing_in_last_bit)
{
    bytes32_t a{};
    a.bytes[31] = 0x00;
    bytes32_t b{};
    b.bytes[31] = 0x01;
    this->apply({{a, value_of(1)}, {b, value_of(2)}});
    this->expect_equal_roots();
}

TYPED_TEST(LbtOracleTest, erase_all_then_reinsert)
{
    std::mt19937_64 rng{4};
    auto const a = random_key(rng);
    auto const b = random_key(rng);
    this->apply({{a, value_of(1)}, {b, value_of(2)}});
    this->apply({{a, std::nullopt}, {b, std::nullopt}});
    EXPECT_EQ(this->engine_root(), bytes32_t{});
    this->expect_equal_roots();
    this->apply({{b, value_of(5)}});
    this->expect_pinned_root(PIN_ERASE_ALL_THEN_REINSERT);
}

TEST(LbtDbRoot, db_root_commitment_matches_reference)
{
    Db db{std::make_unique<KeyedMachine<6>>()};
    ReferenceTrie ref;
    EXPECT_EQ(db_root_commitment(nullptr), ref.root());

    std::mt19937_64 rng{6};
    std::vector<bytes32_t> keys;
    std::vector<byte_string> values;
    for (uint64_t i = 0; i < 200; ++i) {
        keys.push_back(random_key(rng));
        values.push_back(value_of(i));
        ref.upsert(keys.back(), leaf_value(values.back()));
    }
    std::vector<Update> updates;
    updates.reserve(keys.size());
    UpdateList list;
    for (size_t i = 0; i < keys.size(); ++i) {
        updates.push_back(make_update(key_view(keys[i]), values[i]));
        list.push_front(updates.back());
    }
    auto root = db.upsert(nullptr, std::move(list), 0);
    EXPECT_EQ(db_root_commitment(root.get()), ref.root());
    EXPECT_EQ(ref.root(), PIN_DB_ROOT_200_KEYS);

    std::vector<Update> erases;
    erases.reserve(keys.size());
    UpdateList erase_list;
    for (auto const &k : keys) {
        erases.push_back(make_erase(key_view(k)));
        erase_list.push_front(erases.back());
    }
    root = db.upsert(std::move(root), std::move(erase_list), 1);
    EXPECT_EQ(db_root_commitment(root.get()), bytes32_t{});
}

TYPED_TEST(LbtOracleTest, same_value_reupsert_keeps_root)
{
    std::mt19937_64 rng{5};
    auto const a = random_key(rng);
    auto const b = random_key(rng);
    this->apply({{a, value_of(1)}, {b, value_of(2)}});
    auto const r1 = this->engine_root();
    this->apply({{a, value_of(1)}});
    EXPECT_EQ(this->engine_root(), r1);
    this->expect_equal_roots();
}

TYPED_TEST(LbtOracleTest, binds_bits_above_attach_point)
{
    // The lone leaf in nibble 0x0 or 0x1 rises to prefix 0 either way, so
    // only its key tells the two tries apart.
    bytes32_t a{};
    a.bytes[0] = 0x05;
    bytes32_t moved{};
    moved.bytes[0] = 0x15;
    bytes32_t b{};
    b.bytes[0] = 0x80;
    this->apply({{a, value_of(1)}, {b, value_of(2)}});
    this->expect_equal_roots();
    auto const before = this->engine_root();
    this->apply({{a, std::nullopt}, {moved, value_of(1)}});
    this->expect_pinned_root(PIN_BINDS_BITS_ABOVE_ATTACH_POINT);
    EXPECT_NE(this->engine_root(), before);
}

TYPED_TEST(LbtOracleTest, erase_lifts_leaf_from_disk)
{
    // a and b share their first nibble. The fixture caches depths 0 and 1
    // only, so on disk the engine reads b back before lifting it.
    bytes32_t a{};
    a.bytes[0] = 0x21;
    bytes32_t b{};
    b.bytes[0] = 0x2e;
    bytes32_t c{};
    c.bytes[0] = 0x70;
    this->apply({{a, value_of(1)}, {b, value_of(2)}, {c, value_of(3)}});
    this->expect_equal_roots();
    this->apply({{a, std::nullopt}});
    this->expect_pinned_root(PIN_ERASE_LIFTS_LEAF_FROM_DISK);
}

TYPED_TEST(LbtOracleTest, erase_lifts_leaf_across_levels)
{
    // a and b share 40 nibbles; erasing b lifts a over that compressed path.
    bytes32_t a;
    for (auto &byte : a.bytes) {
        byte = 0x33;
    }
    bytes32_t b = a;
    b.bytes[20] = 0x44;
    bytes32_t c{};
    c.bytes[0] = 0x90;
    this->apply({{a, value_of(1)}, {b, value_of(2)}, {c, value_of(3)}});
    this->expect_equal_roots();
    this->apply({{b, std::nullopt}});
    this->expect_pinned_root(PIN_ERASE_LIFTS_LEAF_ACROSS_LEVELS);
}

TEST(LbtComputeDeathTest, set_node_data_without_pending_data_aborts)
{
    lbt::LbtDataCompute compute;
    unsigned char buffer[sizeof(bytes32_t)];
    EXPECT_DEATH((void)compute.set_node_data(buffer, sizeof(buffer)), "");
}
