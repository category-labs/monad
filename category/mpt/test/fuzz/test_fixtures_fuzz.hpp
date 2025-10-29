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

#include "../test_fixtures_base.hpp"

#include "one_hundred_updates.hpp"

#include <category/core/byte_string.hpp>

#include <map>
#include <optional>
#include <span>
#include <type_traits>

namespace monad::test
{
    // Used to force Node's pool to be instanced now, not after the test fixture
    // exits
    static auto force_node_pool_instance_now =
        allocators::aliasing_allocator_pair<Node>();

    namespace detail
    {
        template <class T>
        struct is_std_vector : std::false_type
        {
        };

        template <class T, class Allocator>
        struct is_std_vector<std::vector<T, Allocator>> : std::true_type
        {
        };

        template <class T>
        struct is_std_array : std::false_type
        {
        };

        template <class T, size_t N>
        struct is_std_array<std::array<T, N>> : std::true_type
        {
        };

        template <class T>
        struct is_std_map : std::false_type
        {
        };

        template <class Key, class T, class Compare, class Allocator>
        struct is_std_map<std::map<Key, T, Compare, Allocator>> : std::true_type
        {
        };
    }

    class fuzztest_input_filler
    {
        std::span<uint8_t const> const input_;
        std::span<uint8_t const>::const_iterator cursor_;

        void fill_(uint8_t &what, uint8_t min = 0, uint8_t max = 255)
        {
            if (!input_.empty()) {
                what = (*cursor_++ % (1 + max - min)) + min;
                if (cursor_ == input_.end()) {
                    cursor_ = input_.begin();
                }
            }
        }

    public:
        constexpr fuzztest_input_filler(std::span<uint8_t const> input)
            : input_(input)
            , cursor_(input_.begin())
        {
        }

        template <class T>
            requires(std::is_integral_v<T>)
        T
        get(T min = std::numeric_limits<T>::min(),
            T max = std::numeric_limits<T>::max())
        {
            T ret{};
            if (!input_.empty()) {
                std::span<uint8_t, sizeof(T)> i((uint8_t *)&ret, sizeof(T));
                for (uint8_t &c : i) {
                    fill_(c);
                }
                if (max - min != std::numeric_limits<T>::max()) {
                    ret = (ret % (1 + max - min)) + min;
                }
            }
            return ret;
        }

        template <class T>
            requires(
                detail::is_std_array<T>::value &&
                std::is_trivially_copyable_v<typename T::value_type>)
        T get(typename T::value_type min, typename T::value_type max)
        {
            T ret{};
            if (!input_.empty()) {
                for (auto &i : ret) {
                    i = get<typename T::value_type>(min, max);
                }
            }
            return ret;
        }

        template <class T>
            requires(
                detail::is_std_vector<T>::value &&
                std::is_trivially_copyable_v<typename T::value_type>)
        T
        get(size_t count, typename T::value_type min,
            typename T::value_type max)
        {
            T ret(count);
            if (!input_.empty()) {
                for (auto &i : ret) {
                    i = get<typename T::value_type>(min, max);
                }
            }
            return ret;
        }

        template <class T>
            requires(detail::is_std_map<T>::value)
        T
        get(std::pair<size_t, size_t> count, uint8_t length_min = 0,
            uint8_t length_max = 255)
        {
            T ret{};
            using key_type = typename T::key_type;
            using mapped_type = typename T::mapped_type;
            if (!input_.empty()) {
                if (count.first != count.second) {
                    count.second = get<size_t>(count.first, count.second);
                }
                for (size_t n = 0; n < count.second; n++) {
                    uint8_t length;
                    fill_(length, length_min, length_max);
                    key_type key{};
                    if constexpr (std::
                                      is_same_v<key_type, monad::byte_string>) {
                        key.resize(32);
                        for (auto &i : key) {
                            fill_(i);
                        }
                    }
                    else {
                        key = n;
                    }
                    mapped_type value{};
                    if (length > 0) {
                        monad::byte_string s;
                        s.resize(length);
                        for (auto &i : s) {
                            fill_(i);
                        }
                        value = std::move(s);
                    }
                    ret[key] = value;
                }
            }
            return ret;
        }
    };

    template <typename TFixture>
    struct trie_fuzzer_fixture : public TFixture
    {
        using TFixture::root_hash;

        void Process(
            std::ranges::range auto const &kv,
            std::ranges::range auto const &groups,
            std::map<size_t, std::optional<monad::byte_string>> const &mods)
        {
            MONAD_ASSERT(groups.size() == kv.size());

            std::map<size_t, std::vector<Update>> inputs;
            inputs.emplace(kv.size(), std::vector<Update>{});

            for (size_t i = 0; i < groups.size(); ++i) {
                inputs[groups[i]].emplace_back(
                    make_update(kv[i].first, kv[i].second));
            }

            // Add updates to the next batch of inputs to be processed
            for (size_t i = 0; i < kv.size(); ++i) {
                if (!mods.contains(i)) {
                    continue;
                }

                auto const it = inputs.find(groups[i]);
                MONAD_DEBUG_ASSERT(it != inputs.end());

                auto const next = std::next(it);
                MONAD_DEBUG_ASSERT(next != inputs.end());

                if (mods.at(i).has_value()) {
                    // insert kv of {key[i], random generated value in mods}
                    next->second.emplace_back(
                        make_update(kv[i].first, mods.at(i).value()));
                }
                else {
                    next->second.emplace_back(make_erase(kv[i].first));
                }
            }

            if (inputs[kv.size()].empty()) {
                inputs.erase(kv.size());
            }

            size_t count = 0;
            for (auto &[_, input] : inputs) {
                count += input.size();
                this->root = upsert_vector(
                    this->aux,
                    *this->sm,
                    std::move(this->root),
                    std::move(input));
            }
            MONAD_ASSERT(count >= 100);
        }

        void OneHundredUpdates(
            std::array<size_t, 100> const &groups,
            std::map<size_t, std::optional<monad::byte_string>> const &mods)
        {
            MONAD_DEBUG_ASSERT(this->root.get() == nullptr);
            Process(one_hundred_updates, groups, mods);

            if (!mods.empty()) {
                // Fix the trie so that the root hashes are back to normal
                std::vector<Update> correct;
                for (auto const &[i, _] : mods) {
                    correct.emplace_back(make_update(
                        one_hundred_updates[i].first,
                        one_hundred_updates[i].second));
                }
                this->root = upsert_vector(
                    this->aux,
                    *this->sm,
                    std::move(this->root),
                    std::move(correct));
            }

            MONAD_ASSERT(
                root_hash() ==
                0xcbb6d81afdc76fec144f6a1a283205d42c03c102a94fc210b3a1bcfdcb625884_bytes);
        }

        void GeneratedKv(
            std::map<monad::byte_string, monad::byte_string> const &kv,
            std::vector<size_t> const &groups,
            std::map<size_t, std::optional<monad::byte_string>> const &mods)
        {
            MONAD_DEBUG_ASSERT(this->root.get() == nullptr);
            std::vector<std::pair<monad::byte_string, monad::byte_string>>
                transformed;
            for (auto const &p : kv) {
                transformed.emplace_back(
                    [&]() {
                        MONAD_ASSERT(p.first.size() == 32);
                        monad::byte_string b;
                        b.resize(32);
                        std::copy_n(p.first.data(), 32, b.data());
                        return b;
                    }(),
                    p.second);
            }
            Process(transformed, groups, mods);

            std::vector<Update> updates;
            for (size_t i = 0; i < transformed.size(); ++i) {
                if (mods.contains(i) && !mods.at(i).has_value()) {
                    continue;
                }
                updates.emplace_back(make_erase(transformed[i].first));
            }

            if (!updates.empty()) {
                this->root = upsert_vector(
                    this->aux,
                    *this->sm,
                    std::move(this->root),
                    std::move(updates));
            }
            MONAD_ASSERT(root_hash() == NULL_ROOT);
        }
    };

    struct Nothing
    {
    };

    using in_memory_trie_fixture_t =
        trie_fuzzer_fixture<MerkleTrie<InMemoryTrieBase<void, Nothing>>>;
    using on_disk_fixture_t =
        trie_fuzzer_fixture<MerkleTrie<OnDiskTrieBase<void, Nothing>>>;
}
