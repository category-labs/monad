// Copyright (C) 2026 Category Labs, Inc.
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
#include <category/core/config.hpp>

#include <ankerl/unordered_dense.h>

#include <cstddef>
#include <cstdint>
#include <optional>
#include <ranges>
#include <utility>
#include <vector>

MONAD_NAMESPACE_BEGIN

class JournalCheckpoints
{
    struct Mark
    {
        size_t undo_size;
        uint64_t epoch;
    };

    std::vector<Mark> marks_;
    uint64_t epoch_{0};
    uint64_t last_epoch_{0};

public:
    size_t depth() const
    {
        return marks_.size();
    }

    uint64_t epoch() const
    {
        return epoch_;
    }

    bool needs_save(uint64_t const stamp) const
    {
        return !marks_.empty() && stamp < epoch_;
    }

    size_t undo_size() const
    {
        MONAD_ASSERT(!marks_.empty());
        return marks_.back().undo_size;
    }

    void push(size_t const undo_size)
    {
        marks_.push_back({undo_size, epoch_});
        epoch_ = ++last_epoch_;
    }

    size_t pop()
    {
        MONAD_ASSERT(!marks_.empty());
        auto const [undo_size, epoch] = marks_.back();
        marks_.pop_back();
        epoch_ = epoch;
        return undo_size;
    }
};

template <class K, class V>
class JournaledMap
{
    struct Slot
    {
        V value;
        uint64_t stamp;
    };

    struct Undo
    {
        K key;
        std::optional<V> value;
        uint64_t stamp;
    };

    ankerl::unordered_dense::segmented_map<K, Slot> map_;
    std::vector<Undo> undo_;
    JournalCheckpoints checkpoints_;

    V &save(K const &key, Slot &slot)
    {
        if (checkpoints_.needs_save(slot.stamp)) {
            undo_.push_back({key, slot.value, slot.stamp});
            slot.stamp = checkpoints_.epoch();
        }
        return slot.value;
    }

public:
    size_t size() const
    {
        return map_.size();
    }

    size_t depth() const
    {
        return checkpoints_.depth();
    }

    bool contains(K const &key) const
    {
        return map_.contains(key);
    }

    V const *find(K const &key) const
    {
        auto const it = map_.find(key);
        return it == map_.end() ? nullptr : &it->second.value;
    }

    V *find_writable(K const &key)
    {
        auto const it = map_.find(key);
        return it == map_.end() ? nullptr : &save(it->first, it->second);
    }

    template <class F>
    V &write(K const &key, F &&make)
    {
        if (auto const it = map_.find(key); it != map_.end()) {
            return save(it->first, it->second);
        }
        if (checkpoints_.depth()) {
            undo_.push_back({key, std::nullopt, 0});
        }
        auto const it =
            map_.try_emplace(key, Slot{make(), checkpoints_.epoch()}).first;
        return it->second.value;
    }

    template <class F>
    void write_all(F &&f)
    {
        for (auto &[key, slot] : map_) {
            f(key, save(key, slot));
        }
    }

    auto items() const
    {
        return std::views::iota(size_t{0}, map_.size()) |
               std::views::transform([this](size_t const i) {
                   auto const &entry = map_.values()[i];
                   return std::pair<K const &, V const &>{
                       entry.first, entry.second.value};
               });
    }

    auto keys_since_checkpoint() const
    {
        return undo_ | std::views::drop(checkpoints_.undo_size()) |
               std::views::transform(&Undo::key);
    }

    void checkpoint()
    {
        checkpoints_.push(undo_.size());
    }

    void commit()
    {
        checkpoints_.pop();
        if (!checkpoints_.depth()) {
            undo_.clear();
        }
    }

    void revert()
    {
        auto const undo_size = checkpoints_.pop();
        while (undo_.size() > undo_size) {
            auto &undo = undo_.back();
            if (undo.value.has_value()) {
                auto const it = map_.find(undo.key);
                MONAD_ASSERT(it != map_.end());
                it->second = {std::move(*undo.value), undo.stamp};
            }
            else {
                map_.erase(undo.key);
            }
            undo_.pop_back();
        }
    }
};

template <class T>
class JournaledValue
{
    struct Undo
    {
        T value;
        uint64_t stamp;
    };

    T value_;
    uint64_t stamp_{0};
    std::vector<Undo> undo_;
    JournalCheckpoints checkpoints_;

public:
    explicit JournaledValue(T value = {})
        : value_{std::move(value)}
    {
    }

    size_t depth() const
    {
        return checkpoints_.depth();
    }

    T const &get() const
    {
        return value_;
    }

    T &write()
    {
        if (checkpoints_.needs_save(stamp_)) {
            undo_.push_back({value_, stamp_});
            stamp_ = checkpoints_.epoch();
        }
        return value_;
    }

    void checkpoint()
    {
        checkpoints_.push(undo_.size());
    }

    void commit()
    {
        checkpoints_.pop();
        if (!checkpoints_.depth()) {
            undo_.clear();
        }
    }

    void revert()
    {
        auto const undo_size = checkpoints_.pop();
        while (undo_.size() > undo_size) {
            auto &undo = undo_.back();
            value_ = std::move(undo.value);
            stamp_ = undo.stamp;
            undo_.pop_back();
        }
    }
};

MONAD_NAMESPACE_END
