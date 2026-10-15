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

#pragma once

#include <category/core/lru/static_lru_cache.hpp>
#include <category/mpt/config.hpp>
#include <category/mpt/node.hpp>
#include <category/mpt/trie.hpp>
#include <category/mpt/util.hpp>

#include <chrono>
#include <cstdint>
#include <memory>
#include <optional>

MONAD_MPT_NAMESPACE_BEGIN

//! Apart from a rewind, which reuses tail counts at once, an insertion count
//! is reassigned only once its list's tail comes round to it again. So entries
//! cached since the cache was last emptied cannot alias a later chunk's node
//! before a tail reaches the head count of that moment. A rewind is caught
//! only if a check runs before appends carry the tail back past where it was.
//! Counts compare modulo the period, so a full check that comes more than the
//! fastest possible lap after the previous one forgets everything.
class CountReuseWatch
{
    struct watched_list_
    {
        uint32_t head_when_emptied;
        uint32_t last_tail;
    };

    struct watched_lists_
    {
        watched_list_ fast;
        watched_list_ slow;
    };

    std::optional<watched_lists_> watched_;
    std::chrono::steady_clock::duration fastest_lap_;
    std::optional<std::chrono::steady_clock::time_point> last_check_;

    // A rewound tail ranks almost a whole period past the last one, so it
    // reaches the head too.
    static bool
    tail_reached_(watched_list_ const list, uint32_t const tail) noexcept
    {
        chunk_list_order const from_last_tail{list.last_tail};
        uint32_t const to_head = from_last_tail.rank(list.head_when_emptied);
        return to_head != 0 && to_head <= from_last_tail.rank(tail);
    }

public:
    explicit CountReuseWatch(
        std::chrono::steady_clock::duration const fastest_lap) noexcept
        : fastest_lap_{fastest_lap}
    {
    }

    //! Whether the cache must be emptied, given both lists' counts at `at`.
    //! Unreadable counts (nullopt) always empty it and drop the baseline: the
    //! append before a stalled one may have reassigned a cached count.
    bool must_forget(
        std::optional<fast_slow_list_counts> const now,
        std::chrono::steady_clock::time_point const at) noexcept
    {
        bool const lapsed =
            last_check_.has_value() && at - *last_check_ > fastest_lap_;
        last_check_ = at;
        if (!now.has_value()) {
            watched_.reset();
            return true;
        }
        if (!lapsed && watched_.has_value() &&
            !tail_reached_(watched_->fast, now->fast.tail) &&
            !tail_reached_(watched_->slow, now->slow.tail)) {
            watched_->fast.last_tail = now->fast.tail;
            watched_->slow.last_tail = now->slow.tail;
            return false;
        }
        watched_ = watched_lists_{
            .fast = {now->fast.head, now->fast.tail},
            .slow = {now->slow.head, now->slow.tail}};
        return true;
    }
};

// Memory bounded node cache
class NodeCache final
    : private static_lru_cache<
          virtual_chunk_offset_t, std::pair<std::shared_ptr<Node>, unsigned>,
          virtual_chunk_offset_t_hasher>
{
    // second in value is node size
    using Base = static_lru_cache<
        virtual_chunk_offset_t, std::pair<std::shared_ptr<Node>, unsigned>,
        virtual_chunk_offset_t_hasher>;

    size_t max_bytes_;
    size_t used_bytes_{0};
    UpdateAux const &aux_;
    CountReuseWatch watch_;
    // Every append changes its list's tail id or that chunk's metadata word,
    // as does finishing a stalled append, so while both tail states stay put
    // no cached count can have been reassigned. Two cases skip the full check
    // anyway: a rewind that re-appends the same chunk, and both states
    // repeating exactly a whole lap later with no lookup in between, as a
    // list cycling two chunks can do while the other list stays put.
    std::optional<fast_slow_tail_states> checked_tails_;

    // No pool is written faster than this.
    static constexpr double max_write_bytes_per_second_ = 64.0 * (1ull << 30);

    static std::chrono::steady_clock::duration
    fastest_lap_(UpdateAux const &aux) noexcept
    {
        std::chrono::duration<double> const lap{
            double(INSERTION_COUNT_PERIOD) * double(aux.io->chunk_capacity(0)) /
            max_write_bytes_per_second_};
        return std::chrono::duration_cast<std::chrono::steady_clock::duration>(
            lap);
    }

    void recycle_(list_node &node) noexcept
    {
        node.key = virtual_chunk_offset_t::invalid_value();
        node.val = {nullptr, 0};
        free_list_.push_front(node);
    }

    void evict_until_under_limit()
    {
        while (used_bytes_ > max_bytes_ && !active_list_.empty()) {
            auto const list_it = std::prev(active_list_.end());
            auto &node_to_erase = *list_it;
            map_.erase(list_it->key);
            used_bytes_ -= list_it->val.second;
            active_list_.erase(list_it);
            recycle_(node_to_erase);
        }
    }

    void forget_all_() noexcept
    {
        map_.clear();
        while (!active_list_.empty()) {
            auto &node = active_list_.front();
            active_list_.pop_front();
            recycle_(node);
        }
        used_bytes_ = 0;
    }

    void forget_if_counts_reused_() noexcept
    {
        auto const tails = aux_.list_tail_states();
        if (checked_tails_ == tails) {
            return;
        }
        if (watch_.must_forget(
                aux_.list_counts(), std::chrono::steady_clock::now())) {
            forget_all_();
        }
        checked_tails_ = tails;
    }

public:
    static constexpr size_t AVERAGE_NODE_SIZE = 104;

    using Base::ConstAccessor;
    using Base::list_node;

    using Base::size;

    NodeCache(size_t const max_bytes, UpdateAux const &aux)
        : Base(
              max_bytes / AVERAGE_NODE_SIZE,
              virtual_chunk_offset_t::invalid_value(), {nullptr, 0})
        , max_bytes_(max_bytes)
        , used_bytes_{0}
        , aux_{aux}
        , watch_{fastest_lap_(aux)}
    {
        MONAD_ASSERT(aux.is_on_disk());
        // Entries inserted before the first lookup need a baseline too.
        forget_if_counts_reused_();
    }

    ~NodeCache() = default;

    // Checking on every lookup, rather than once per root, orders the tail
    // reads after the caller resolved the offset it looks up, so they see
    // every append that preceded it.
    bool find(ConstAccessor &acc, virtual_chunk_offset_t const &key) noexcept
    {
        forget_if_counts_reused_();
        return Base::find(acc, key);
    }

    Map::iterator insert(
        virtual_chunk_offset_t const &virt_offset,
        std::shared_ptr<Node> const &sp) noexcept
    {
        MONAD_ASSERT(virt_offset != virtual_chunk_offset_t::invalid_value());

        used_bytes_ += sp->get_mem_size();
        evict_until_under_limit();

        auto const [it, erased_value] =
            Base::insert(virt_offset, {sp, sp->get_mem_size()});
        if (erased_value.has_value()) {
            used_bytes_ -= erased_value->second;
        }
        return it;
    }
};

MONAD_MPT_NAMESPACE_END
