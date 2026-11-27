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

#pragma once

#include "test_fixtures_base.hpp"
#include "test_fixtures_gtest.hpp"

#include <category/core/byte_string.hpp>
#include <category/core/small_prng.hpp>
#include <category/mpt/config.hpp>
#include <category/mpt/detail/timeline.hpp>
#include <category/mpt/trie.hpp>
#include <category/mpt/update.hpp>

#include <cstddef>
#include <cstdint>
#include <cstring>
#include <deque>
#include <utility>
#include <vector>

namespace monad::test
{
    // 64 chunks of 8 MiB in a file, so disk_usage() reaches high values
    // quickly; a short fixed history keeps chunk freeing prompt.
    constexpr FillDBWithChunksConfig PRESSURE_POOL{
        .chunks_to_fill = 1,
        .chunks_max = 64,
        .history_len = 64,
        .updates_per_block = 100,
        .use_anonymous_inode = false};

    using PoolState = FillDBWithChunks<PRESSURE_POOL, ::testing::Test>::state_t;

    inline constexpr uint8_t BULK_PREFIX = 0x00;
    inline constexpr uint8_t FIFO_PREFIX = 0xFF;

    inline byte_string random_key(small_prng &rng, uint8_t const prefix)
    {
        byte_string key(32, 0);
        for (size_t i = 0; i < key.size(); i += 4) {
            uint32_t const v = rng();
            std::memcpy(key.data() + i, &v, sizeof(v));
        }
        key[0] = prefix;
        return key;
    }

    inline void pool_upsert(
        PoolState &state, mpt::UpdateList &&updates, uint64_t const version,
        bool const compaction, bool const can_write_to_fast)
    {
        state.root = state.aux.do_update(
            std::move(state.root),
            state.sm,
            std::move(updates),
            version,
            compaction,
            can_write_to_fast,
            /*write_root=*/true,
            mpt::timeline_id::primary);
    }

    // Writes batches until disk_usage() reaches `usage`: straight to the slow
    // list, as a snapshot load does, unless `can_write_to_fast`. Every batch
    // is live unless `rewrite_same_keys`, which leaves one batch live and the
    // rest superseded. Each batch also rewrites the interior nodes above its
    // keys, so fewer, larger batches leave less garbage behind.
    inline void bulk_load_to(
        PoolState &state, double const usage, size_t const value_size,
        bool const can_write_to_fast, bool const rewrite_same_keys = false,
        size_t const batch = 4096)
    {
        small_prng rng{1};
        byte_string const value(value_size, 0xab);
        while (state.aux.disk_usage() < usage) {
            if (rewrite_same_keys) {
                rng = small_prng{1};
            }
            std::vector<byte_string> keys;
            std::vector<mpt::Update> updates;
            keys.reserve(batch);
            updates.reserve(batch);
            mpt::UpdateList ls;
            for (size_t i = 0; i < batch; ++i) {
                keys.push_back(random_key(rng, BULK_PREFIX));
                updates.push_back(mpt::make_update(keys.back(), value));
                ls.push_front(updates.back());
            }
            pool_upsert(
                state,
                std::move(ls),
                state.version++,
                /*compaction=*/false,
                can_write_to_fast);
        }
    }

    // Each block inserts `inserts` keys and deletes the keys inserted
    // `lifetime` blocks earlier, so live data stays bounded and every key
    // copied to the slow list eventually becomes garbage there.
    class FifoWorkload
    {
        size_t inserts_;
        size_t lifetime_;
        byte_string value_;
        small_prng rng_;
        std::deque<std::vector<byte_string>> live_;

    public:
        FifoWorkload(
            size_t const inserts, size_t const value_size,
            size_t const lifetime, uint32_t const seed)
            : inserts_{inserts}
            , lifetime_{lifetime}
            , value_(value_size, 0xcd)
            , rng_{seed}
        {
        }

        void run_block(PoolState &state)
        {
            std::vector<byte_string> fresh;
            fresh.reserve(inserts_);
            std::vector<byte_string> expired;
            if (live_.size() == lifetime_) {
                expired = std::move(live_.front());
                live_.pop_front();
            }
            std::vector<mpt::Update> updates;
            updates.reserve(inserts_ + expired.size());
            mpt::UpdateList ls;
            for (size_t i = 0; i < inserts_; ++i) {
                fresh.push_back(random_key(rng_, FIFO_PREFIX));
                updates.push_back(mpt::make_update(fresh.back(), value_));
                ls.push_front(updates.back());
            }
            for (auto const &key : expired) {
                updates.push_back(mpt::make_erase(key));
                ls.push_front(updates.back());
            }
            pool_upsert(
                state,
                std::move(ls),
                state.version++,
                /*compaction=*/true,
                /*can_write_to_fast=*/true);
            live_.push_back(std::move(fresh));
        }
    };
}
