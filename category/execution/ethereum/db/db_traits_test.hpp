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

#include <category/execution/ethereum/db/trie_db.hpp>
#include <category/execution/ethereum/db/util.hpp>
#include <category/mpt/ondisk_db_config.hpp>
#include <category/vm/evm/traits.hpp>
#include <category/vm/vm.hpp>
#include <monad/test/traits_test.hpp>

#include <gtest/gtest.h>

using namespace monad;

namespace
{
    template <typename T, T rev>
    struct TrieDbFixtureTraits : public ::testing::Test
    {
        vm::VM vm;

        static constexpr auto get_trait()
        {
            if constexpr (std::same_as<T, monad_revision>) {
                return monad::MonadTraits<rev>{};
            }
            else if constexpr (std::same_as<T, evmc_revision>) {
                return monad::EvmTraits<rev>{};
            }
            else {
                return std::monostate{};
            }
        }

        using Trait = decltype(get_trait());

        static consteval bool is_monad_trait() noexcept
        {
            return monad::is_monad_trait_v<Trait>;
        }

        static consteval bool is_evm_trait() noexcept
        {
            return monad::is_evm_trait_v<Trait>;
        }

        static constexpr std::string get_traits_name()
        {
            if constexpr (std::same_as<T, monad_revision>) {
                return "/" + std::string(monad_revision_to_string(
                                 monad::MonadTraits<rev>::monad_rev()));
            }
            else if constexpr (std::same_as<T, evmc_revision>) {
                return "/" + std::string(evmc_revision_to_string(
                                 monad::EvmTraits<rev>::evm_rev()));
            }
            else {
                return "";
            }
        }
    };

    template <typename T, T rev>
    struct InMemoryTrieDbFixtureTraits : public TrieDbFixtureTraits<T, rev>
    {
        static constexpr bool on_disk = false;

        InMemoryMachine machine;
        mpt::Db db{machine};
        TrieDb tdb{db};

        static constexpr auto get_name()
        {
            return "InMemoryTrieDbFixture" +
                   TrieDbFixtureTraits<T, rev>::get_traits_name();
        }
    };

    template <monad_revision rev>
    using MonadInMemoryTrieDbFixtureTraits =
        InMemoryTrieDbFixtureTraits<monad_revision, rev>;

    template <evmc_revision rev>
    using EvmInMemoryTrieDbFixtureTraits =
        InMemoryTrieDbFixtureTraits<evmc_revision, rev>;

    template <typename T, T rev>
    struct OnDiskTrieDbFixtureTraits : public TrieDbFixtureTraits<T, rev>
    {
        static constexpr bool on_disk = true;

        OnDiskMachine machine;
        mpt::Db db{machine, mpt::OnDiskDbConfig{}};
        TrieDb tdb{db};

        static constexpr auto get_name()
        {
            return "OnDiskTrieDbFixture" +
                   TrieDbFixtureTraits<T, rev>::get_traits_name();
        }
    };

    template <monad_revision rev>
    using MonadOnDiskTrieDbFixtureTraits =
        OnDiskTrieDbFixtureTraits<monad_revision, rev>;

    template <evmc_revision rev>
    using EvmOnDiskTrieDbFixtureTraits =
        OnDiskTrieDbFixtureTraits<evmc_revision, rev>;

    // Helper to concatenate four ::testing::Types
    template <typename... Ts>
    struct concat_types;

    template <
        typename... Ts1, typename... Ts2, typename... Ts3, typename... Ts4>
    struct concat_types<
        ::testing::Types<Ts1...>, ::testing::Types<Ts2...>,
        ::testing::Types<Ts3...>, ::testing::Types<Ts4...>>
    {
        using type = ::testing::Types<Ts1..., Ts2..., Ts3..., Ts4...>;
    };

    template <typename... Ts>
    using concat_types_t = typename concat_types<Ts...>::type;

    // Union of MonadRevisionTypes and EvmRevisionTypes for both InMemoryTrieDb
    // and OnDiskTrieDb
    using MonadEvmRevisionDBTypes = concat_types_t<
        decltype(make_monad_revision_types<MonadInMemoryTrieDbFixtureTraits>()),
        decltype(make_evm_revision_types<EvmInMemoryTrieDbFixtureTraits>()),
        decltype(make_monad_revision_types<MonadOnDiskTrieDbFixtureTraits>()),
        decltype(make_evm_revision_types<EvmOnDiskTrieDbFixtureTraits>())>;

    struct RevisionTestNameGenerator
    {
        template <typename T>
        static std::string GetName(int)
        {
            return T::get_name();
        }
    };
}

using InMemoryTrieDbFixture = InMemoryTrieDbFixtureTraits<std::monostate, {}>;
using OnDiskTrieDbFixture = OnDiskTrieDbFixtureTraits<std::monostate, {}>;

template <typename TDB>
struct DBTest : public TDB
{
};

using DBTypes = ::testing::Types<InMemoryTrieDbFixture, OnDiskTrieDbFixture>;
TYPED_TEST_SUITE(DBTest, DBTypes, RevisionTestNameGenerator);

template <typename TDB>
struct DBTraitsTest : public TDB
{
};

TYPED_TEST_SUITE(
    DBTraitsTest, MonadEvmRevisionDBTypes, RevisionTestNameGenerator);
