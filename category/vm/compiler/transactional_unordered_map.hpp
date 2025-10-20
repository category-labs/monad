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

#include <category/vm/core/assert.h>

#include <optional>
#include <unordered_map>
#include <vector>

namespace monad::vm::compiler
{
    template <
        typename K, typename V, typename Hash = std::hash<K>,
        typename KeyEqual = std::equal_to<K>>
    class TransactionalUnorderedMap
    {
        struct Entry
        {
            K key;
            std::optional<V> prev_value;
        };

        using Map = std::unordered_map<K, V, Hash, KeyEqual>;

        Map current;
        std::vector<Entry> journal;
        std::vector<size_t> checkpoints;

        void push_checkpoint(K const &k)
        {
            if (!checkpoints.empty()) {
                auto const it = current.find(k);
                if (it != current.end()) {
                    journal.emplace_back(k, std::move(it->second));
                }
                else {
                    journal.emplace_back(k, std::nullopt);
                }
            }
        }

    public:
        using value_type = Map::value_type;
        using iterator = Map::iterator;
        using const_iterator = Map::const_iterator;

        TransactionalUnorderedMap()
            : current{}
        {
        }

        TransactionalUnorderedMap(std::initializer_list<value_type> init)
            : current(init)
        {
        }

        V const &at(K const &k) const
        {
            return current.at(k);
        }

        V find_or_default(K const &k) const
        {
            auto const it = find(k);
            if (it == end()) {
                return V();
            }
            return it->second;
        }

        iterator find(K const &k)
        {
            return current.find(k);
        }

        const_iterator find(K const &k) const
        {
            return current.find(k);
        }

        iterator begin()
        {
            return current.begin();
        }

        iterator end()
        {
            return current.end();
        }

        const_iterator begin() const
        {
            return current.begin();
        }

        const_iterator end() const
        {
            return current.end();
        }

        bool contains(K const &k) const
        {
            return current.contains(k);
        }

        bool erase(K const &k)
        {
            push_checkpoint(k);
            return current.erase(k) == 1;
        }

        template <typename M>
        bool put(K const &k, M &&v)
        {
            push_checkpoint(k);
            return current.insert_or_assign(k, std::forward<M>(v)).second;
        }

        void transaction()
        {
            checkpoints.push_back(journal.size());
        }

        void commit()
        {
            MONAD_VM_DEBUG_ASSERT(!checkpoints.empty());
            checkpoints.pop_back();
        }

        void revert()
        {
            MONAD_VM_DEBUG_ASSERT(!checkpoints.empty());

            size_t const last_point = checkpoints.back();
            checkpoints.pop_back();

            while (journal.size() > last_point) {
                auto &entry = journal.back();
                if (entry.prev_value.has_value()) {
                    current.insert_or_assign(
                        entry.key, std::move(*entry.prev_value));
                }
                else {
                    current.erase(entry.key);
                }
                journal.pop_back();
            }
        }
    };
}
