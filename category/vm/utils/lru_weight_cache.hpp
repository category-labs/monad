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

#include <category/core/assert.h>

#include <tbb/concurrent_hash_map.h>

#include <atomic>
#include <chrono>
#include <mutex>
#include <optional>
#include <string>
#include <utility>

#include <unordered_set>

namespace monad::vm::utils
{
    // LRU Cache in which elements can have different weights. It is based
    // on the LruCache in monad.
    template <
        class Key, class Value,
        class KeyHashCompare = tbb::tbb_hash_compare<Key>>
    class LruWeightCache
    {
        /// TYPES
        class LruList;
        struct HashMapValue;
        using ListNode = std::pair<Key const, HashMapValue>;
        using HashMap =
            tbb::concurrent_hash_map<Key, HashMapValue, KeyHashCompare>;
        using Accessor = HashMap::accessor;

        /// DATA
        uint32_t max_weight_;
        std::atomic<int64_t> weight_;
        LruList lru_;
        HashMap hmap_;
        // Stamp mode: an entry has a value flag (negative_) and a region
        // flag (stamped_: the time field is its consensus stamp, written only
        // by set_stamp at finalize). Stamped entries, with or without a value,
        // sit at the head of the list in stamp order; unstamped live entries
        // behind the boundary sentinel in insertion order; unstamped negative
        // entries on the negative list. Eviction drains unstamped entries
        // first, then stamps oldest first, so a cached victim (stamp >= the
        // evict floor) means the cached set outgrew the capacity; eviction
        // asserts it. The weight budget covers everything on the live list.
        bool const stamp_mode_{false};
        std::atomic<uint64_t> evict_floor_{0};
        // negative entries sit on their own count-budgeted list; the shared
        // weight budget covers live entries only
        size_t const negative_max_{0};
        std::atomic<size_t> negative_size_{0};
        LruList negative_lru_;
        std::atomic<size_t> stamped_negative_{0};

    public:
        using ConstAccessor = HashMap::const_accessor;

        explicit LruWeightCache(
            uint32_t const max_weight,
            std::chrono::nanoseconds const lru_update_duration =
                std::chrono::milliseconds{200},
            bool const stamp_mode = false, size_t const negative_max = 0)
            : max_weight_(max_weight)
            , weight_(0)
            , lru_{lru_update_duration.count(), stamp_mode}
            , stamp_mode_{stamp_mode}
            , negative_max_{negative_max}
            , negative_lru_{lru_update_duration.count()}
        {
        }

        LruWeightCache(LruWeightCache const &) = delete;
        LruWeightCache &operator=(LruWeightCache const &) = delete;

        bool find(ConstAccessor &acc, Key const &key)
        {
            if (!hmap_.find(acc, key)) {
                return false;
            }
            if (!stamp_mode_) {
                try_update_lru(lru_, &*acc);
            }
            else if (!acc->second.stamped_) {
                // the unstamped regions are plain LRUs (a read promotes,
                // rate limited); stamped entries never move on a read
                if (acc->second.negative_) {
                    negative_lru_.try_update_unstamped_negative(&*acc);
                }
                else {
                    lru_.try_update_unstamped_live(&*acc);
                }
            }
            return true;
        }

        bool is_negative(ConstAccessor const &acc) const
        {
            return acc->second.negative_;
        }

        // Consensus stamp of an entry; 0 = unstamped.
        uint64_t stamp_of(ConstAccessor const &acc) const
        {
            if (!acc->second.stamped_) {
                return 0;
            }
            return static_cast<uint64_t>(
                acc->second.lru_time_.load(std::memory_order_acquire));
        }

        size_t stamped_negative_count() const
        {
            return stamped_negative_.load(std::memory_order_relaxed);
        }

        size_t negative_count() const
        {
            return negative_size_.load(std::memory_order_relaxed);
        }

        // Finalize path: set the consensus stamp of a resident entry (with or
        // without a value) and move it to the front of the stamped region.
        // Returns false when the entry is not resident.
        bool set_stamp(Key const &key, uint64_t const stamp)
        {
            ConstAccessor acc;
            if (!hmap_.find(acc, key)) {
                return false;
            }
            ListNode const *const node = &*acc;
            auto const moved = lru_.stamp_from(
                negative_lru_, node, static_cast<int64_t>(stamp));
            if (moved == LruList::Moved::none) {
                return false;
            }
            if (moved == LruList::Moved::from_negative_list) {
                stamped_negative_.fetch_add(1, std::memory_order_relaxed);
                negative_size_.fetch_sub(1, std::memory_order_acq_rel);
                adjust_by_delta_weight(node->second.cache_weight_);
            }
            return true;
        }

        // Death record (finalize / bootstrap): forget the stamp of a resident
        // entry; a live entry moves to the front of the unstamped region, an
        // empty one to the negative list.
        bool clear_stamp(Key const &key)
        {
            ConstAccessor acc;
            if (!hmap_.find(acc, key)) {
                return false;
            }
            ListNode const *const node = &*acc;
            auto const moved = lru_.unstamp_to(negative_lru_, node);
            if (moved == LruList::Moved::to_negative_list) {
                stamped_negative_.fetch_sub(1, std::memory_order_relaxed);
                weight_.fetch_sub(
                    node->second.cache_weight_, std::memory_order_acq_rel);
                trim_negative(
                    1 + negative_size_.fetch_add(1, std::memory_order_acq_rel));
            }
            return moved != LruList::Moved::none;
        }

        void set_evict_floor(uint64_t const floor)
        {
            evict_floor_.store(floor, std::memory_order_relaxed);
        }

        // Finalize path, after the floor advanced: entries whose stamp fell
        // below it leave the stamped region (live ones to the front of the
        // unstamped region — touched within the last window, they are more
        // recent than most entries there — empty ones to the negative list),
        // so the stamped region is exactly the cached set and expired stamps
        // cannot crowd out fresh inserts.
        void demote_expired(uint64_t const floor)
        {
            int64_t weight_out = 0;
            size_t to_negative = 0;
            lru_.demote_expired(
                negative_lru_, floor, [&](ListNode const *const node) {
                    weight_out += node->second.cache_weight_;
                    ++to_negative;
                });
            if (to_negative != 0) {
                stamped_negative_.fetch_sub(
                    to_negative, std::memory_order_relaxed);
                weight_.fetch_sub(weight_out, std::memory_order_acq_rel);
                size_t const sz = negative_size_.fetch_add(
                                      to_negative, std::memory_order_acq_rel) +
                                  to_negative;
                for (size_t i = negative_max_; i < sz; ++i) {
                    if (!evict_negative()) {
                        break;
                    }
                    negative_size_.fetch_sub(1, std::memory_order_acq_rel);
                }
            }
        }

        /// Insert `value` with `weight` under `key`. Overwrites if there is
        /// already a value under `key`. In stamp mode `negative` selects the
        /// list; a changed flag flips the entry in place.
        bool insert(
            Key const &key, Value const &value, uint32_t const weight,
            bool const negative = false)
        {
            bool const neg = stamp_mode_ && negative;
            Accessor acc;
            if (!hmap_.insert(acc, {key, HashMapValue{value, weight, neg}})) {
                ListNode *const node = &*acc;
                bool const was_negative = node->second.negative_;
                // the weight budget covers the live list: unstamped live
                // entries and every stamped entry
                bool const stamped = stamp_mode_ && node->second.stamped_;
                bool const on_live_before = stamped || !was_negative;
                bool const on_live_after = stamped || !neg;
                int64_t delta_weight = on_live_after ? weight : 0;
                if (on_live_before) {
                    delta_weight -= node->second.cache_weight_;
                }
                using std::swap;
                Value tmp = value;
                swap(node->second.value_, tmp);
                node->second.cache_weight_ = weight;
                if (!stamp_mode_) {
                    try_update_lru(lru_, node);
                }
                else if (was_negative != neg) {
                    if (stamped) {
                        lru_.set_negative_flag(node, neg);
                        stamped_negative_.fetch_add(
                            neg ? 1 : static_cast<size_t>(-1),
                            std::memory_order_relaxed);
                    }
                    else {
                        transition(node, neg);
                    }
                }
                acc.release();
                if (delta_weight != 0) {
                    adjust_by_delta_weight(delta_weight);
                }
                return false;
            }
            ListNode *const node = &*acc;
            acc.release();
            if (neg) {
                negative_lru_.push_front(node);
                trim_negative(
                    1 + negative_size_.fetch_add(1, std::memory_order_acq_rel));
            }
            else {
                push_live(node);
                adjust_by_delta_weight(weight);
            }
            return true;
        }

        // Not thread-safe with other cache operations.
        void clear()
        {
            hmap_.clear();
            lru_.clear();
            negative_lru_.clear();
            weight_.store(0, std::memory_order_release);
            negative_size_.store(0, std::memory_order_release);
        }

        /// Like insert, but does not overwrite an existing value in the cache.
        /// Instead if a value already exists under `key` then it will
        /// overwrite the `value` argument with the existing value.
        bool try_insert(Key const &key, Value &value, uint32_t const weight)
        {
            ConstAccessor acc;
            if (!hmap_.insert(acc, {key, HashMapValue{value, weight, false}})) {
                value = acc->second.value_;
                if (!stamp_mode_) {
                    try_update_lru(lru_, &*acc);
                }
                return false;
            }
            ListNode const *const node = &*acc;
            acc.release();
            lru_.push_front(node);
            adjust_by_delta_weight(weight);
            return true;
        }

        /// Like try_insert, but takes `value` by const reference and never
        /// mutates it or overwrites an existing entry. Returns true iff a new
        /// entry was inserted.
        bool try_insert_no_overwrite(
            Key const &key, Value const &value, uint32_t const weight,
            bool const negative = false)
        {
            bool const neg = stamp_mode_ && negative;
            ConstAccessor acc;
            if (!hmap_.insert(acc, {key, HashMapValue{value, weight, neg}})) {
                if (!stamp_mode_) {
                    try_update_lru(lru_, &*acc);
                }
                else if (acc->second.negative_ && !acc->second.stamped_) {
                    negative_lru_.try_update_unstamped_negative(&*acc);
                }
                return false;
            }
            ListNode const *const node = &*acc;
            acc.release();
            if (neg) {
                negative_lru_.push_front(node);
                trim_negative(
                    1 + negative_size_.fetch_add(1, std::memory_order_acq_rel));
            }
            else {
                push_live(node);
                adjust_by_delta_weight(weight);
            }
            return true;
        }

        /// Get approximate total weight of the cached elements.
        uint64_t approx_weight() const
        {
            return static_cast<uint64_t>(
                weight_.load(std::memory_order_acquire));
        }

        /// Return the number of cached elements.
        size_t size() const noexcept
        {
            return hmap_.size();
        }

        // For testing: to check internal invariants. Not safe with
        // concurrent `insert` calls.
        bool unsafe_check_consistent()
        {
            return lru_.unsafe_check_consistent(hmap_, weight_.load());
        }

    private:
        // A new live entry: unstamped, behind the boundary in stamp mode.
        void push_live(ListNode const *const node)
        {
            if (stamp_mode_) {
                lru_.push_unstamped(node);
            }
            else {
                lru_.push_front(node);
            }
        }

        void adjust_by_delta_weight(int64_t const delta_weight)
        {
            int64_t const pre_weight =
                weight_.fetch_add(delta_weight, std::memory_order_acq_rel);
            if (delta_weight + pre_weight > max_weight_) {
                int64_t evicted_weight = 0;
                while (evicted_weight < delta_weight) {
                    auto const n = evict_from(lru_);
                    if (MONAD_UNLIKELY(!n.has_value())) {
                        break;
                    }
                    weight_.fetch_sub(*n, std::memory_order_acq_rel);
                    evicted_weight += *n;
                }
            }
        }

        // Evict the tail of `list` and return its weight, or nullopt when the
        // list is empty. The map accessor is taken before the node leaves the
        // list, and the node is delinked only if it is still the tail once
        // the accessor is held: a reader that found the entry in the map
        // either sees it in the list (and can promote it, after which the
        // eviction moves on to the new tail) or does not find it at all, so
        // an entry a block read can never vanish before finalize stamps it.
        std::optional<uint32_t> evict_from(LruList &list)
        {
            while (true) {
                auto const candidate = list.tail_candidate();
                if (!candidate.has_value()) {
                    return std::nullopt;
                }
                auto const &[key, target] = *candidate;
                Accessor acc;
                if (!hmap_.find(acc, key) || &*acc != target) {
                    continue; // evicted by another thread meanwhile
                }
                if (!list.remove_if_tail(target)) {
                    continue; // promoted (or gone) meanwhile: retry
                }
                if (stamp_mode_ && target->second.stamped_) {
                    // unstamped entries drain first, then stamps oldest
                    // first: a cached victim means the cached set outgrew
                    // the physical capacity — a consensus bug, not a perf bug
                    uint64_t const stamp =
                        static_cast<uint64_t>(target->second.lru_time_.load(
                            std::memory_order_acquire));
                    MONAD_ASSERT(
                        stamp < evict_floor_.load(std::memory_order_relaxed));
                    if (target->second.negative_) {
                        stamped_negative_.fetch_sub(
                            1, std::memory_order_relaxed);
                    }
                }
                uint32_t const wt = acc->second.cache_weight_;
                hmap_.erase(acc);
                return wt;
            }
        }

        void try_update_lru(LruList &list, ListNode const *const node)
        {
            if (node->second.check_lru_time(list.now())) {
                list.update_lru(node);
            }
        }

        // Flip an entry between the live and negative lists in place
        // (finalize path: the value was created or deleted). Weight and count
        // budgets are adjusted by the caller via delta_weight/trim.
        void transition(ListNode *const node, bool const negative)
        {
            if (!(negative ? negative_lru_ : lru_)
                     .relink_from(
                         negative ? lru_ : negative_lru_,
                         node,
                         negative,
                         /*behind_boundary=*/!negative && stamp_mode_)) {
                return; // being evicted concurrently
            }
            if (negative) {
                trim_negative(
                    1 + negative_size_.fetch_add(1, std::memory_order_acq_rel));
            }
            else {
                negative_size_.fetch_sub(1, std::memory_order_acq_rel);
            }
        }

        void trim_negative(size_t const size)
        {
            if (size > negative_max_ && evict_negative()) {
                negative_size_.fetch_sub(1, std::memory_order_acq_rel);
            }
        }

        bool evict_negative()
        {
            return evict_from(negative_lru_).has_value();
        }

        /// HashMapValue
        struct HashMapValue
        {
            mutable ListNode const *prev_{};
            mutable ListNode const *next_{};
            mutable std::atomic<int64_t> lru_time_{0};
            Value value_;
            uint32_t cache_weight_;
            mutable bool negative_{false}; // the key holds no value
            mutable bool stamped_{false}; // stamped region; time is the stamp

            HashMapValue() = default;

            HashMapValue(
                Value const &value, uint32_t const weight,
                bool const negative = false)
                : value_{value}
                , cache_weight_{weight}
                , negative_{negative}
            {
            }

            // For insert into tbb hash map:
            HashMapValue(HashMapValue &&x) noexcept
                : prev_{x.prev_}
                , next_{x.next_}
                , lru_time_{x.lru_time_.load(std::memory_order_relaxed)}
                , value_{std::move(x.value_)}
                , cache_weight_{x.cache_weight_}
                , negative_{x.negative_}
                , stamped_{x.stamped_}
            {
            }

            bool is_in_list() const
            {
                return prev_ != nullptr;
            }

            void update_lru_time(int64_t const next_allowed) const
            {
                lru_time_.store(next_allowed, std::memory_order_release);
            }

            bool check_lru_time(int64_t const now) const
            {
                return now >= lru_time_.load(std::memory_order_acquire);
            }

            static int64_t wall_clock()
            {
                return std::chrono::duration_cast<std::chrono::nanoseconds>(
                           std::chrono::steady_clock::now().time_since_epoch())
                    .count();
            }
        }; /// HashMapValue

        /// LruList
        class LruList
        {
            ListNode base_;
            // stamp mode: sentinel between the stamped region (ahead) and
            // the unstamped region (behind); never evicted
            ListNode boundary_;
            std::mutex mutex_;
            int64_t lru_update_period_;
            bool const with_boundary_;

        public:
            explicit LruList(
                int64_t const lru_update_period,
                bool const with_boundary = false)
                : lru_update_period_{lru_update_period}
                , with_boundary_{with_boundary}
            {
                clear();
            }

            int64_t now() const
            {
                return ListNode::second_type::wall_clock();
            }

            int64_t next_allowed() const
            {
                return now() + lru_update_period_;
            }

            // Not thread-safe with other LruList operations.
            void clear()
            {
                base_.second.next_ = &base_;
                base_.second.prev_ = &base_;
                if (with_boundary_) {
                    front_link(&boundary_);
                }
            }

            void update_lru(ListNode const *const node)
            {
                std::unique_lock const l(mutex_);
                if (node->second.is_in_list()) {
                    delink(node);
                    front_link(node);
                    node->second.update_lru_time(next_allowed());
                } // else item is being evicted or inserted, don't update LRU
            }

            void push_front(ListNode const *const node)
            {
                std::unique_lock const l(mutex_);
                front_link(node);
                node->second.update_lru_time(lru_update_period_);
            }

            // Stamp mode: a new live entry enters the unstamped region,
            // right behind the boundary, with stamp 0.
            void push_unstamped(ListNode const *const node)
            {
                std::unique_lock const l(mutex_);
                link_after(&boundary_, node);
                node->second.update_lru_time(0);
            }

            enum class Moved
            {
                none, // not in any list (being evicted)
                in_place, // already where it belongs
                from_negative_list, // entered this (live) list
                to_negative_list, // left this list for the negative list
            };

            // Stamp mode: stamp `node`, moving it to the front of the stamped
            // region from wherever it is (this list's unstamped region, or
            // the negative list `neg`).
            Moved stamp_from(
                LruList &neg, ListNode const *const node, int64_t const stamp)
            {
                std::scoped_lock const l(mutex_, neg.mutex_);
                if (!node->second.is_in_list()) {
                    return Moved::none;
                }
                bool const from_negative =
                    node->second.negative_ && !node->second.stamped_;
                (from_negative ? neg : *this).delink(node);
                node->second.stamped_ = true;
                front_link(node);
                node->second.update_lru_time(stamp);
                return from_negative ? Moved::from_negative_list
                                     : Moved::in_place;
            }

            // Stamp mode: forget the stamp; a live entry goes behind the
            // boundary, an empty one to the negative list `neg`.
            Moved unstamp_to(LruList &neg, ListNode const *const node)
            {
                std::scoped_lock const l(mutex_, neg.mutex_);
                if (!node->second.is_in_list()) {
                    return Moved::none;
                }
                if (!node->second.stamped_) {
                    return Moved::in_place;
                }
                delink(node);
                node->second.stamped_ = false;
                if (node->second.negative_) {
                    neg.front_link(node);
                    node->second.update_lru_time(
                        ListNode::second_type::wall_clock());
                    return Moved::to_negative_list;
                }
                link_after(&boundary_, node);
                node->second.update_lru_time(0);
                return Moved::in_place;
            }

            // Stamp mode: move every stamped entry with stamp < floor out of
            // the stamped region (they are its tail): live ones behind the
            // boundary, empty ones onto `neg`, reporting each of the latter.
            template <class OnNegative>
            void demote_expired(
                LruList &neg, uint64_t const floor, OnNegative const &on_neg)
            {
                std::scoped_lock const l(mutex_, neg.mutex_);
                while (true) {
                    ListNode const *const node = boundary_.second.prev_;
                    if (node == &base_ || !node->second.stamped_ ||
                        static_cast<uint64_t>(node->second.lru_time_.load(
                            std::memory_order_acquire)) >= floor) {
                        break;
                    }
                    delink(node);
                    node->second.stamped_ = false;
                    if (node->second.negative_) {
                        neg.front_link(node);
                        node->second.update_lru_time(
                            ListNode::second_type::wall_clock());
                        on_neg(node);
                    }
                    else {
                        link_after(&boundary_, node);
                        node->second.update_lru_time(next_allowed());
                    }
                }
            }

            // Stamp mode: change the value flag of a stamped entry in place.
            void set_negative_flag(ListNode const *const node, bool const neg)
            {
                std::unique_lock const l(mutex_);
                node->second.negative_ = neg;
            }

            // Rate-limited promotion of an unstamped live entry to the front
            // of the unstamped region, re-checked under the lock.
            void try_update_unstamped_live(ListNode const *const node)
            {
                if (!node->second.check_lru_time(now())) {
                    return;
                }
                std::unique_lock const l(mutex_);
                if (node->second.is_in_list() && !node->second.negative_ &&
                    !node->second.stamped_) {
                    delink(node);
                    link_after(&boundary_, node);
                    node->second.update_lru_time(next_allowed());
                }
            }

            // Rate-limited recency bump of an entry on the negative list,
            // re-checked under the lock (a finalize may have stamped it).
            void try_update_unstamped_negative(ListNode const *const node)
            {
                if (!node->second.check_lru_time(now())) {
                    return;
                }
                std::unique_lock const l(mutex_);
                if (node->second.is_in_list() && node->second.negative_ &&
                    !node->second.stamped_) {
                    delink(node);
                    front_link(node);
                    node->second.update_lru_time(next_allowed());
                }
            }

            // Move a node from `src` onto this list's front, updating the
            // negative flag and resetting the time field (fresh recency for
            // negatives, unstamped for live). False when the node is not in
            // any list (a concurrent eviction already claimed it).
            bool relink_from(
                LruList &src, ListNode const *const node, bool const negative,
                bool const behind_boundary)
            {
                std::scoped_lock const l(mutex_, src.mutex_);
                if (!node->second.is_in_list()) {
                    return false;
                }
                src.delink(node);
                node->second.negative_ = negative;
                node->second.update_lru_time(
                    negative ? ListNode::second_type::wall_clock() : 0);
                if (behind_boundary) {
                    link_after(&boundary_, node);
                }
                else {
                    front_link(node);
                }
                return true;
            }

            // The tail, skipping the boundary sentinel (unstamped entries
            // drain first, then the stamped region oldest stamp first), with
            // a copy of its key; nullopt when empty. Does not delink.
            std::optional<std::pair<Key, ListNode const *>> tail_candidate()
            {
                std::unique_lock const l(mutex_);
                ListNode const *const target = tail_locked();
                if (target == nullptr) {
                    return std::nullopt;
                }
                return std::make_pair(target->first, target);
            }

            // Delink `node` iff it is still the tail (nothing promoted or
            // removed it since tail_candidate).
            bool remove_if_tail(ListNode const *const node)
            {
                std::unique_lock const l(mutex_);
                if (!node->second.is_in_list() || tail_locked() != node) {
                    return false;
                }
                delink(node);
                node->second.prev_ = nullptr;
                return true;
            }

            bool
            unsafe_check_consistent(HashMap const &hmap, int64_t const weight)
            {
                std::unordered_set<Key> keys;
                std::unique_lock l(mutex_);
                ListNode const *node = base_.second.next_;
                int64_t node_weight = 0;
                while (node != &base_) {
                    if (node == &boundary_) {
                        node = node->second.next_;
                        continue;
                    }
                    auto [_, inserted] = keys.insert(node->first);
                    if (!inserted) {
                        return false;
                    }
                    ConstAccessor acc;
                    bool found = hmap.find(acc, node->first);
                    MONAD_ASSERT(found);
                    node_weight += acc->second.cache_weight_;
                    node = node->second.next_;
                }
                return node_weight == weight;
            }

        private:
            ListNode const *tail_locked() const
            {
                ListNode const *target = base_.second.prev_;
                if (with_boundary_ && target == &boundary_) {
                    target = boundary_.second.prev_;
                }
                return target == &base_ ? nullptr : target;
            }

            void delink(ListNode const *const node)
            {
                ListNode const *const prev = node->second.prev_;
                ListNode const *const next = node->second.next_;
                prev->second.next_ = next;
                next->second.prev_ = prev;
            }

            void front_link(ListNode const *const node)
            {
                link_after(&base_, node);
            }

            void
            link_after(ListNode const *const pos, ListNode const *const node)
            {
                ListNode const *const next = pos->second.next_;
                node->second.prev_ = pos;
                node->second.next_ = next;
                next->second.prev_ = node;
                pos->second.next_ = node;
            }
        }; /// LruList
    }; /// LruWeightCache
}
