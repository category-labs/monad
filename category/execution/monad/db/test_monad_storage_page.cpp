// Copyright (C) 2025 Category Labs, Inc.
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

#include <category/execution/ethereum/db/trie_db.hpp>
#include <category/execution/monad/db/storage_page.hpp>

#include <gtest/gtest.h>

#include <test_resource_data.h>

#include <algorithm>
#include <cstring>

using namespace monad;
using namespace monad::mpt;
using namespace monad::test;

TEST(MonadDb, key_grouping)
{
    // Keys 0x00..0x7F should all map to the same page (page_key = 0)
    bytes32_t const page_key_0 = compute_page_key(bytes32_t{uint64_t{0}});

    for (uint64_t i = 0; i < 128; ++i) {
        bytes32_t const slot_key{i};
        EXPECT_EQ(compute_page_key(slot_key), page_key_0)
            << "slot " << i << " should map to same page as slot 0";
        EXPECT_EQ(compute_slot_offset(slot_key), i)
            << "slot " << i << " should have offset equal to its low bits";
    }

    // Key 0x80 should map to a different page
    bytes32_t const slot_128{uint64_t{0x80}};
    EXPECT_NE(compute_page_key(slot_128), page_key_0);
    EXPECT_EQ(compute_slot_offset(slot_128), 0);

    // Keys 0x80..0xFF should share a second page
    bytes32_t const page_key_1 = compute_page_key(bytes32_t{uint64_t{0x80}});
    for (uint64_t i = 0x80; i < 0x100; ++i) {
        bytes32_t const slot_key{i};
        EXPECT_EQ(compute_page_key(slot_key), page_key_1);
        EXPECT_EQ(
            compute_slot_offset(slot_key),
            static_cast<uint8_t>(i & storage_page_t::SLOT_OFFSET_MASK));
    }

    // Round-trip for all keys 0..0xFF
    for (uint64_t i = 0; i < 256; ++i) {
        bytes32_t const slot_key{i};
        bytes32_t const pk = compute_page_key(slot_key);
        uint8_t const off = compute_slot_offset(slot_key);
        EXPECT_EQ(compute_slot_key(pk, off), slot_key);
    }
}

TEST(MonadDb, page_commit_deterministic)
{
    storage_page_t page{};
    auto const c1 = page_commit(page);
    auto const c2 = page_commit(page);
    EXPECT_EQ(c1, c2);
    EXPECT_NE(c1, bytes32_t{});
}

TEST(MonadDb, page_commit_differs_for_different_pages)
{
    storage_page_t page_a{};
    storage_page_t page_b{};
    page_b.set(0, bytes32_t{0x01});

    EXPECT_NE(page_commit(page_a), page_commit(page_b));
}

TEST(MonadDb, page_commit_sensitive_to_slot_position)
{
    storage_page_t page_a{};
    page_a.set(0, bytes32_t{0x01});

    storage_page_t page_b{};
    page_b.set(1, bytes32_t{0x01});

    EXPECT_NE(page_commit(page_a), page_commit(page_b));
}

TEST(MonadDb, page_commit_sensitive_to_distant_slots)
{
    storage_page_t page_a{};
    page_a.set(0, bytes32_t{0x01});

    storage_page_t page_b{};
    page_b.set(127, bytes32_t{0x01});

    EXPECT_NE(page_commit(page_a), page_commit(page_b));
}

TEST(MonadDb, page_commit_sparse_nonzero)
{
    auto const filled = [](uint8_t const v) {
        bytes32_t b{};
        std::ranges::fill(b.bytes, v);
        return b;
    };
    storage_page_t page{};
    page.set(0, filled(0x11));
    page.set(2, filled(0x22));
    page.set(4, filled(0x33));

    storage_page_t zero_page{};
    EXPECT_NE(page_commit(page), page_commit(zero_page));
    EXPECT_EQ(page_commit(page), page_commit(page));
}

TEST(MonadDb, page_commit_uniform_fill_differs)
{
    auto const filled = [](uint8_t const v) {
        bytes32_t b{};
        std::ranges::fill(b.bytes, v);
        return b;
    };
    storage_page_t page_a{};
    storage_page_t page_b{};
    for (uint8_t i = 0; i < storage_page_t::SLOTS; ++i) {
        page_a.set(i, filled(0x11));
        page_b.set(i, filled(0x22));
    }

    EXPECT_NE(page_commit(page_a), page_commit(page_b));
}

TEST(MonadDb, page_commit_cross_check_with_reference)
{
    constexpr auto ZERO_PAGE_COMMIT =
        0xe572dff82304700b856a555ac3a4558d0df3646a3727816500270a93c66aac1e_bytes32;
    constexpr auto SLOT0_ONE_COMMIT =
        0x80218c63919cd8c68aa9a5c0117bb8b46eb02099a7ce0b47a36e7b21658cc9f9_bytes32;
    constexpr auto SLOT127_ONE_COMMIT =
        0x39a2175f8fac8fbf447383b46ff40e03673b388c05c87e50ed7b3f1a810c98d8_bytes32;
    constexpr auto FULL_PAGE_COMMIT =
        0xe5a642261a2c2dedebd68ebd42237f2210d1eee94553d677d425dc3a46c7a687_bytes32;

    storage_page_t zero_page{};
    EXPECT_EQ(page_commit(zero_page), ZERO_PAGE_COMMIT);

    storage_page_t page_slot0{};
    page_slot0.set(0, bytes32_t{0x01});
    EXPECT_EQ(page_commit(page_slot0), SLOT0_ONE_COMMIT);

    storage_page_t page_slot127{};
    page_slot127.set(127, bytes32_t{0x01});
    EXPECT_EQ(page_commit(page_slot127), SLOT127_ONE_COMMIT);

    storage_page_t full_page{};
    for (uint8_t i = 0; i < 128; ++i) {
        full_page.set(i, bytes32_t{static_cast<uint64_t>(i + 1)});
    }
    EXPECT_EQ(page_commit(full_page), FULL_PAGE_COMMIT);
}

// Sweep across pair-population densities. For each k, fill the first k pairs
// (left slot only). Verifies: (a) the algorithm runs without error at each
// density, (b) commits are deterministic, (c) every density produces a
// distinct hash. Catches regressions in the merge tree at densities that the
// fixed-input cross-check above doesn't exercise.
TEST(MonadDb, page_commit_density_sweep)
{
    constexpr size_t densities[] = {1, 2, 4, 8, 16, 32, 40, 48, 56, 60, 63, 64};
    constexpr size_t N = sizeof(densities) / sizeof(densities[0]);

    bytes32_t hashes[N];

    for (size_t i = 0; i < N; ++i) {
        size_t const k = densities[i];
        storage_page_t page{};
        for (size_t j = 0; j < k; ++j) {
            page.set(
                static_cast<uint8_t>(j * 2),
                bytes32_t{static_cast<uint64_t>(j + 1)});
        }

        auto const c1 = page_commit(page);
        auto const c2 = page_commit(page);
        EXPECT_EQ(c1, c2) << "non-deterministic at k=" << k;
        EXPECT_NE(c1, bytes32_t{}) << "all-zero commit at k=" << k;

        hashes[i] = c1;
    }

    for (size_t i = 0; i < N; ++i) {
        for (size_t j = i + 1; j < N; ++j) {
            EXPECT_NE(hashes[i], hashes[j])
                << "density " << densities[i] << " collides with density "
                << densities[j];
        }
    }
}

// Within a single pair (slots 2k and 2k+1 form pair k), data placed in the
// left slot vs the right slot must produce distinct commitments. The seal's
// slot_bitmap differs (bit 2k vs bit 2k+1) and the leaf hash input differs
// in byte order (data||zeros vs zeros||data). Tested on a non-trivial pair
// index to exercise mid-page indexing.
TEST(MonadDb, page_commit_asymmetric_pair)
{
    constexpr uint8_t pair_idx = 5;
    constexpr uint8_t left_slot = pair_idx * 2;
    constexpr uint8_t right_slot = pair_idx * 2 + 1;

    bytes32_t pattern_aa{};
    std::ranges::fill(pattern_aa.bytes, static_cast<uint8_t>(0xAA));

    storage_page_t left_only{};
    left_only.set(left_slot, pattern_aa);

    storage_page_t right_only{};
    right_only.set(right_slot, pattern_aa);

    auto const c_left = page_commit(left_only);
    auto const c_right = page_commit(right_only);

    EXPECT_NE(c_left, c_right);
    EXPECT_NE(c_left, bytes32_t{});
    EXPECT_NE(c_right, bytes32_t{});
}
