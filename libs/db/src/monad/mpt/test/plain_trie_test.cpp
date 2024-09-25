#include "test_fixtures_base.hpp"
#include "test_fixtures_gtest.hpp" // NOLINT

#include <monad/core/byte_string.hpp>
#include <monad/core/hex_literal.hpp>
#include <monad/mpt/node.hpp>
#include <monad/mpt/trie.hpp>
#include <monad/mpt/update.hpp>

#include <monad/test/gtest_signal_stacktrace_printer.hpp> // NOLINT

#include <chrono>
#include <utility>
#include <vector>

using namespace monad::mpt;
using namespace monad::literals;
using namespace monad::test;

template <typename TFixture>
struct PlainTrieTest : public TFixture
{
};

using PlainTrieTypes = ::testing::Types<InMemoryTrieGTest, OnDiskTrieGTest>;
TYPED_TEST_SUITE(PlainTrieTest, PlainTrieTypes);

namespace updates
{
    std::vector<std::pair<monad::byte_string, monad::byte_string>> const kv{
        {0x01111111_hex, 0xdead_hex}, // 0
        {0x11111111_hex, 0xbeef_hex}, // 1
        {0x11111111aaaa_hex, 0xdeafbeef_hex}, // 2
        {0x11111111aacd_hex, 0xabcd_hex}, // 3
        {0x111a1111_hex, 0xba_hex}, // 4
        {0x111b1111_hex, 0xbabe_hex}, // 5
        {0x111b1111aaaaaaaa_hex, 0xcafe_hex}, // 6
        {0x111b1111bbbbbbbb_hex, 0xbe_hex}, // 7
    };
}

TYPED_TEST(PlainTrieTest, leaf_nodes_persist)
{
    this->root = upsert_updates(
        this->aux,
        *this->sm,
        std::move(this->root),
        make_update(0x11_hex, monad::byte_string_view{}),
        make_update(0x1111_hex, monad::byte_string_view{}),
        make_update(0x1122_hex, monad::byte_string_view{}));
    EXPECT_EQ(this->root->mask, 0b110);

    this->root = upsert_updates(
        this->aux, *this->sm, std::move(this->root), make_erase(0x1111_hex));
    EXPECT_EQ(this->root->mask, 0b100);
}

TYPED_TEST(PlainTrieTest, var_length)
{
    constexpr uint64_t version = 0;
    auto const &kv = updates::kv;
    // insert kv 0,1,2,3
    this->root = upsert_updates(
        this->aux,
        *this->sm,
        std::move(this->root),
        make_update(kv[0].first, kv[0].second),
        make_update(kv[1].first, kv[1].second),
        make_update(kv[2].first, kv[2].second),
        make_update(kv[3].first, kv[3].second));

    EXPECT_EQ(
        find_blocking(this->aux, *this->root, kv[0].first, version)
            .first.node->value(),
        kv[0].second);
    EXPECT_EQ(
        find_blocking(this->aux, *this->root, kv[1].first, version)
            .first.node->value(),
        kv[1].second);
    EXPECT_EQ(
        find_blocking(this->aux, *this->root, kv[2].first, version)
            .first.node->value(),
        kv[2].second);
    EXPECT_EQ(
        find_blocking(this->aux, *this->root, kv[3].first, version)
            .first.node->value(),
        kv[3].second);

    EXPECT_EQ(this->root->mask, 0b11);
    EXPECT_EQ(this->root->value_len, 0);
    EXPECT_EQ(this->root->bitpacked.data_len, 0);
    EXPECT_EQ(this->root->path_bytes(), 0);
    Node *node0 = this->root->next(0);
    Node *node1 = this->root->next(1);
    EXPECT_EQ(node0->mask, 0);
    EXPECT_EQ(
        node0->path_nibble_view(), (NibblesView{1, 8, kv[0].first.data()}));
    EXPECT_EQ(node0->value(), kv[0].second);
    EXPECT_EQ(node1->mask, 1u << 0xa);
    EXPECT_EQ(
        node1->path_nibble_view(), (NibblesView{1, 8, kv[1].first.data()}));
    EXPECT_EQ(node1->value(), kv[1].second);
    Node *node1aa = node1->next(0);
    EXPECT_EQ(node1aa->mask, 1u << 0xa | 1u << 0xc);
    EXPECT_EQ(
        node1aa->path_nibble_view(), (NibblesView{9, 10, kv[3].first.data()}));

    EXPECT_EQ(node1aa->path_bytes(), 1);
    EXPECT_EQ(node1aa->value_len, 0);
    Node *node1aaaa = node1aa->next(0);
    Node *node1aacd = node1aa->next(1);
    EXPECT_EQ(node1aaaa->mask, 0);
    EXPECT_EQ(
        node1aaaa->path_nibble_view(),
        (NibblesView{11, 12, kv[2].first.data()}));
    EXPECT_EQ(node1aaaa->value(), kv[2].second);
    EXPECT_EQ(node1aacd->mask, 0);
    EXPECT_EQ(
        node1aacd->path_nibble_view(),
        (NibblesView{11, 12, kv[3].first.data()}));
    EXPECT_EQ(node1aacd->value(), kv[3].second);

    // insert kv 4,5
    this->root = upsert_updates(
        this->aux,
        *this->sm,
        std::move(this->root),
        make_update(kv[4].first, kv[4].second),
        make_update(kv[5].first, kv[5].second));
    EXPECT_EQ(
        find_blocking(this->aux, *this->root, kv[0].first, version)
            .first.node->value(),
        kv[0].second);
    EXPECT_EQ(
        find_blocking(this->aux, *this->root, kv[1].first, version)
            .first.node->value(),
        kv[1].second);
    EXPECT_EQ(
        find_blocking(this->aux, *this->root, kv[2].first, version)
            .first.node->value(),
        kv[2].second);
    EXPECT_EQ(
        find_blocking(this->aux, *this->root, kv[3].first, version)
            .first.node->value(),
        kv[3].second);
    EXPECT_EQ(
        find_blocking(this->aux, *this->root, kv[4].first, version)
            .first.node->value(),
        kv[4].second);
    EXPECT_EQ(
        find_blocking(this->aux, *this->root, kv[5].first, version)
            .first.node->value(),
        kv[5].second);

    EXPECT_EQ(this->root->mask, 0b11);
    node1 = this->root->next(1); // 1111... 111a... 111b...
    EXPECT_EQ(node1->mask, 1u << 1 | 1u << 0xa | 1u << 0xb);
    Node *node1111 = node1->next(0);
    Node *node111a = node1->next(1);
    Node *node111b = node1->next(2);
    EXPECT_EQ(node1111->value(), kv[1].second);
    EXPECT_EQ(
        node111a->path_nibble_view(), (NibblesView{4, 8, kv[4].first.data()}));
    EXPECT_EQ(node111a->value(), kv[4].second);
    EXPECT_EQ(node111b->value(), kv[5].second);

    // insert kv 6,7
    this->root = upsert_updates(
        this->aux,
        *this->sm,
        std::move(this->root),
        make_update(kv[6].first, kv[6].second),
        make_update(kv[7].first, kv[7].second));
    EXPECT_EQ(
        find_blocking(this->aux, *this->root, kv[5].first, version)
            .first.node->value(),
        kv[5].second);
    EXPECT_EQ(
        find_blocking(this->aux, *this->root, kv[6].first, version)
            .first.node->value(),
        kv[6].second);
    EXPECT_EQ(
        find_blocking(this->aux, *this->root, kv[7].first, version)
            .first.node->value(),
        kv[7].second);

    node1 = this->root->next(this->root->to_child_index(1));
    node111b = node1->next(node1->to_child_index(0xb));
    EXPECT_EQ(node111b->mask, 1u << 0xa | 1u << 0xb);
    EXPECT_EQ(
        node111b->next(node111b->to_child_index(0xa))->value(), kv[6].second);
    EXPECT_EQ(
        node111b->next(node111b->to_child_index(0xa))->path_nibble_view(),
        (NibblesView{9, 16, kv[6].first.data()}));
    EXPECT_EQ(
        node111b->next(node111b->to_child_index(0xb))->value(), kv[7].second);
    EXPECT_EQ(
        node111b->next(node111b->to_child_index(0xb))->path_nibble_view(),
        (NibblesView{9, 16, kv[7].first.data()}));
}

TYPED_TEST(PlainTrieTest, mismatch)
{
    constexpr uint64_t version = 0;
    std::vector<std::pair<monad::byte_string, monad::byte_string>> const kv{
        {0x12345678_hex, 0xdead_hex}, // 0
        {0x12346678_hex, 0xbeef_hex}, // 1
        {0x12445678_hex, 0xdeafbeef_hex}, // 2
        {0x12347678_hex, 0xba_hex}, // 3
        {0x123aabcd_hex, 0xbabe_hex}, // 4
    };

    /* insert 12345678, 12346678, 12445678
            12
          /    \
         34      445678
        / \
    5678  6678
    */
    this->root = upsert_updates(
        this->aux,
        *this->sm,
        std::move(this->root),
        make_update(kv[0].first, kv[0].second),
        make_update(kv[1].first, kv[1].second),
        make_update(kv[2].first, kv[2].second));
    EXPECT_EQ(
        find_blocking(this->aux, *this->root, kv[0].first, version)
            .first.node->value(),
        kv[0].second);
    EXPECT_EQ(
        find_blocking(this->aux, *this->root, kv[1].first, version)
            .first.node->value(),
        kv[1].second);
    EXPECT_EQ(
        find_blocking(this->aux, *this->root, kv[2].first, version)
            .first.node->value(),
        kv[2].second);

    EXPECT_EQ(this->root->mask, 0b11000);
    EXPECT_EQ(
        this->root->path_nibble_view(),
        (NibblesView{0, 2, kv[0].first.data()}));
    EXPECT_EQ(this->root->next(1)->value(), kv[2].second);
    Node *left_leaf = this->root->next(0)->next(0);
    EXPECT_EQ(left_leaf->value(), kv[0].second);
    /* insert 12347678, 123aabcd
                  12
                /    \
              3       445678
             / \
            4   aabcd
          / | \
      5678 6678 7678
    */
    this->root = upsert_updates(
        this->aux,
        *this->sm,
        std::move(this->root),
        make_update(kv[3].first, kv[3].second),
        make_update(kv[4].first, kv[4].second));
    EXPECT_EQ(
        find_blocking(this->aux, *this->root, kv[1].first, version)
            .first.node->value(),
        kv[1].second);
    EXPECT_EQ(
        find_blocking(this->aux, *this->root, kv[2].first, version)
            .first.node->value(),
        kv[2].second);
    EXPECT_EQ(
        find_blocking(this->aux, *this->root, kv[3].first, version)
            .first.node->value(),
        kv[3].second);
    EXPECT_EQ(
        find_blocking(this->aux, *this->root, kv[4].first, version)
            .first.node->value(),
        kv[4].second);

    EXPECT_EQ(this->root->mask, 0b11000);
    EXPECT_EQ(
        this->root->path_nibble_view(),
        (NibblesView{0, 2, kv[0].first.data()}));
    Node *node3 = this->root->next(0);
    EXPECT_EQ(node3->mask, 1u << 4 | 1u << 0xa);
    EXPECT_EQ(node3->bitpacked.data_len, 0);
    EXPECT_EQ(node3->path_bytes(), 0);
    Node *node34 = node3->next(0);
    EXPECT_EQ(node34->mask, 0b11100000);
    EXPECT_EQ(node34->bitpacked.data_len, 0);
    EXPECT_EQ(node34->path_bytes(), 0);
    EXPECT_EQ(node34->next(0)->value_len, 2);
    EXPECT_EQ(node34->next(0)->value(), kv[0].second);
    EXPECT_EQ(node34->next(1)->value(), kv[1].second);
    EXPECT_EQ(node34->next(2)->value(), kv[3].second);
}

TYPED_TEST(PlainTrieTest, delete_wo_incarnation)
{
    auto const &kv = updates::kv;

    // insert all
    this->root = upsert_updates(
        this->aux,
        *this->sm,
        std::move(this->root),
        make_update(kv[0].first, kv[0].second),
        make_update(kv[1].first, kv[1].second),
        make_update(kv[2].first, kv[2].second),
        make_update(kv[3].first, kv[3].second),
        make_update(kv[4].first, kv[4].second),
        make_update(kv[5].first, kv[5].second),
        make_update(kv[6].first, kv[6].second),
        make_update(kv[7].first, kv[7].second));
    // erase 0
    this->root = upsert_updates(
        this->aux, *this->sm, std::move(this->root), make_erase(kv[0].first));
    EXPECT_EQ(this->root->mask, 2 | 1u << 0xa | 1u << 0xb);
    EXPECT_EQ(
        this->root->path_nibble_view(),
        (NibblesView{0, 3, kv[1].first.data()}));

    // erase 5, a leaf with children (consequently 6 and 7 are erased)
    this->root = upsert_updates(
        this->aux, *this->sm, std::move(this->root), make_erase(kv[5].first));
    EXPECT_EQ(this->root->mask, 2 | 1u << 0xa);
    EXPECT_EQ(
        this->root->path_nibble_view(),
        (NibblesView{0, 3, kv[1].first.data()}));

    // erase 1, consequently 2,3 are erased
    this->root = upsert_updates(
        this->aux, *this->sm, std::move(this->root), make_erase(kv[1].first));
    EXPECT_EQ(this->root->mask, 0);
    EXPECT_EQ(this->root->value(), kv[4].second);
    EXPECT_EQ(
        this->root->path_nibble_view(),
        (NibblesView{0, 8, kv[4].first.data()}));
}

TYPED_TEST(PlainTrieTest, delete_with_incarnation)
{
    constexpr uint64_t version = 0;
    // upsert a bunch of var lengths kv
    auto const &kv = updates::kv;
    // insert
    this->root = upsert_updates(
        this->aux,
        *this->sm,
        std::move(this->root),
        make_update(kv[0].first, kv[0].second), // 0x01111111
        make_update(kv[1].first, kv[1].second), // 0x11111111
        make_update(kv[2].first, kv[2].second)); // 0x11111111aaaa
    EXPECT_EQ(
        find_blocking(this->aux, *this->root, kv[0].first, version)
            .first.node->value(),
        kv[0].second);
    EXPECT_EQ(
        find_blocking(this->aux, *this->root, kv[1].first, version)
            .first.node->value(),
        kv[1].second);
    EXPECT_EQ(
        find_blocking(this->aux, *this->root, kv[2].first, version)
            .first.node->value(),
        kv[2].second);

    // upsert a bunch of new kvs, with incarnation flag set
    this->root = upsert_updates(
        this->aux,
        *this->sm,
        std::move(this->root),
        make_update(kv[1].first, kv[1].second, true), // 0x11111111
        make_update(kv[3].first, kv[3].second)); // 0x11111111aacd
    EXPECT_EQ(
        find_blocking(this->aux, *this->root, kv[0].first, version)
            .first.node->value(),
        kv[0].second);
    EXPECT_EQ(
        find_blocking(this->aux, *this->root, kv[1].first, version)
            .first.node->value(),
        kv[1].second);
    EXPECT_EQ(
        find_blocking(this->aux, *this->root, kv[3].first, version)
            .first.node->value(),
        kv[3].second);
    EXPECT_EQ(
        find_blocking(this->aux, *this->root, kv[2].first, version).second,
        find_result::key_mismatch_failure);
}

TYPED_TEST(PlainTrieTest, large_values)
{
    constexpr uint64_t version = 0;
    // make sure leaves are not cached
    auto const key1 = 0x0000112_hex;
    auto const key2 = 0x0000123_hex;
    auto const value1 = monad::byte_string(100 * 1024 * 1024, 0xf); // 100 MB
    auto const value2 = monad::byte_string(255 * 1024 * 1024, 0x3); // 255 MB

    auto same_upsert_to_clear_nodes_outside_cache_level = [&] {
        this->root = upsert_updates(
            this->aux,
            *this->sm,
            std::move(this->root),
            make_update(key1, value1),
            make_update(key2, value2));
    };

    same_upsert_to_clear_nodes_outside_cache_level();
    {
        auto [leaf_it, res] =
            find_blocking(this->aux, *this->root, key1, version);
        auto *leaf = leaf_it.node;
        EXPECT_EQ(res, find_result::success);
        EXPECT_NE(leaf, nullptr);
        EXPECT_TRUE(leaf->has_value());
        EXPECT_EQ(leaf->value(), value1);
    }

    same_upsert_to_clear_nodes_outside_cache_level();
    {
        auto [leaf_it, res] =
            find_blocking(this->aux, *this->root, key2, version);
        auto *leaf = leaf_it.node;
        EXPECT_EQ(res, find_result::success);
        EXPECT_NE(leaf, nullptr);
        EXPECT_TRUE(leaf->has_value());
        EXPECT_EQ(leaf->value(), value2);
    }

    same_upsert_to_clear_nodes_outside_cache_level();
    {
        DbSyncObject sync;
        find_cursor_result_type result;

        inflight_map_t inflights;
        fiber_find_request_t const req{&sync, &result, *this->root, key1};
        find_notify_fiber_future(this->aux, inflights, req);
        while (!sync.try_acquire()) {
            this->aux.io->wait_until_done();
        }
        auto [leaf_it, res] = result;
        auto *leaf = leaf_it.node;
        EXPECT_EQ(res, find_result::success);
        EXPECT_NE(leaf, nullptr);
        EXPECT_TRUE(leaf->has_value());
        EXPECT_EQ(leaf->value(), value1);
    }

    same_upsert_to_clear_nodes_outside_cache_level();
    {
        DbSyncObject sync;
        find_cursor_result_type result;

        inflight_map_t inflights;
        fiber_find_request_t const req{&sync, &result, *this->root, key2};
        find_notify_fiber_future(this->aux, inflights, req);
        while (!sync.try_acquire()) {
            this->aux.io->wait_until_done();
        }
        auto [leaf_it, res] = result;
        auto *leaf = leaf_it.node;
        EXPECT_EQ(res, find_result::success);
        EXPECT_NE(leaf, nullptr);
        EXPECT_TRUE(leaf->has_value());
        EXPECT_EQ(leaf->value(), value2);
    }

    same_upsert_to_clear_nodes_outside_cache_level();
}

TYPED_TEST(PlainTrieTest, multi_level_find_blocking)
{
    constexpr uint64_t version = 0;
    // upsert a bunch of var lengths kv
    auto const &kv = updates::kv;
    // always insert the same updates to the second level trie
    Update u1 = make_update(kv[0].first, kv[0].second); // 0x01111111
    Update u2 = make_update(kv[1].first, kv[1].second); // 0x11111111
    Update u3 = make_update(kv[2].first, kv[2].second); // 0x11111111aaaa

    auto upsert_and_find_with_prefix = [&](monad::byte_string const prefix,
                                           monad::byte_string const top_value) {
        UpdateList updates;
        updates.push_front(u1);
        updates.push_front(u2);
        updates.push_front(u3);
        // insert
        this->root = upsert_updates(
            this->aux,
            *this->sm,
            std::move(this->root),
            make_update(prefix, top_value, false, std::move(updates)));
        // find blocking on multi-level trie
        auto [begin, errc] =
            find_blocking(this->aux, *this->root, prefix, version);
        EXPECT_EQ(errc, find_result::success);
        EXPECT_EQ(begin.node->number_of_children(), 2);
        EXPECT_EQ(begin.node->value(), top_value);

        EXPECT_EQ(
            find_blocking(this->aux, begin, kv[0].first, version)
                .first.node->value(),
            kv[0].second);
        EXPECT_EQ(
            find_blocking(this->aux, begin, kv[1].first, version)
                .first.node->value(),
            kv[1].second);
        EXPECT_EQ(
            find_blocking(this->aux, begin, kv[2].first, version)
                .first.node->value(),
            kv[2].second);
    };

    upsert_and_find_with_prefix(0x000001_hex, 0xdeadbeef_hex);
    upsert_and_find_with_prefix(0x000002_hex, 0x0123456789_hex);
    upsert_and_find_with_prefix(0x000003_hex, 0x9876543210_hex);
    upsert_and_find_with_prefix(0x000004_hex, 0xdeadbeef_hex);
}

TYPED_TEST(PlainTrieTest, node_version)
{
    // Verify node verisons after multiple upserts
    std::vector<monad::byte_string> const keys = {
        0x000000_hex, 0x000001_hex, 0x000002_hex, 0x000010_hex, 0x000011_hex};
    auto const value = 0xdeadbeaf_hex;

    this->root = upsert_updates(
        this->aux,
        *this->sm,
        std::move(this->root),
        make_update(keys[0], value, false, {}, 0));
    this->root = upsert_updates(
        this->aux,
        *this->sm,
        std::move(this->root),
        make_update(keys[1], value, false, {}, 1));
    this->root = upsert_updates(
        this->aux,
        *this->sm,
        std::move(this->root),
        make_update(keys[2], value, false, {}, 2));

    EXPECT_EQ(this->root->version, 2);

    auto read_child = [&](Node &parent,
                          unsigned const index) -> Node::UniquePtr {
        return read_node_blocking(this->aux, parent.fnext(index), 0);
    };
    if (this->root->next(0)) {
        EXPECT_EQ(this->root->next(0)->version, 0);
    }
    else {
        EXPECT_EQ(read_child(*this->root, 0)->version, 0);
    }

    if (this->root->next(1)) {
        EXPECT_EQ(this->root->next(1)->version, 1);
    }
    else {
        EXPECT_EQ(read_child(*this->root, 1)->version, 1);
    }

    if (this->root->next(2)) {
        EXPECT_EQ(this->root->next(2)->version, 2);
    }
    else {
        EXPECT_EQ(read_child(*this->root, 2)->version, 2);
    }

    this->root = upsert_updates(
        this->aux,
        *this->sm,
        std::move(this->root),
        make_update(keys[3], value, false, {}, 3));
    EXPECT_EQ(this->root->version, 3);
    if (this->root->next(0)) {
        EXPECT_EQ(this->root->next(0)->version, 2);
    }
    else {
        EXPECT_EQ(read_child(*this->root, 0)->version, 2);
    }
    if (this->root->next(1)) {
        EXPECT_EQ(this->root->next(1)->version, 3);
    }
    else {
        EXPECT_EQ(read_child(*this->root, 1)->version, 3);
    }

    this->root = upsert_updates(
        this->aux,
        *this->sm,
        std::move(this->root),
        make_update(keys[4], value, false, {}, 4));
    EXPECT_EQ(this->root->version, 4);
    if (this->root->next(0)) {
        EXPECT_EQ(this->root->next(0)->version, 2);
    }
    else {
        EXPECT_EQ(read_child(*this->root, 0)->version, 2);
    }

    if (!this->root->next(1)) {
        this->root->set_next(1, read_child(*this->root, 1));
    }
    EXPECT_EQ(this->root->next(1)->version, 4);

    if (this->root->next(1)->next(0)) {
        EXPECT_EQ(this->root->next(1)->next(0)->version, 3);
    }
    else {
        EXPECT_EQ(read_child(*this->root->next(1), 0)->version, 3);
    }

    // erase should not update the version of interior nodes
    this->root = upsert_updates(
        this->aux, *this->sm, std::move(this->root), make_erase(keys[4]));
    EXPECT_EQ(this->root->version, 4);
    EXPECT_NE(this->root->next(1), nullptr);
    EXPECT_EQ(this->root->next(1)->version, 4);
    EXPECT_NE(this->root->next(0), nullptr);
    EXPECT_EQ(this->root->next(0)->version, 2);
}
