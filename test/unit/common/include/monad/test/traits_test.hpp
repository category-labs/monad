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

#include <category/vm/evm/monad/revision.h>
#include <category/vm/evm/traits.hpp>

#include <evmc/evmc.h>
#include <gtest/gtest.h>

#include <format>
#include <type_traits>
#include <utility>

namespace detail
{
    template <monad_revision rev>
    using MonadRevisionConstant = std::integral_constant<monad_revision, rev>;

    template <evmc_revision rev>
    using EvmRevisionConstant = std::integral_constant<evmc_revision, rev>;

    template <std::size_t... Is>
    constexpr auto make_monad_revision_types(std::index_sequence<Is...>)
    {
        return ::testing::Types<
            MonadRevisionConstant<static_cast<monad_revision>(Is)>...>{};
    }

    template <std::size_t... Is>
    constexpr auto make_evm_revision_types(std::index_sequence<Is...>)
    {
        return ::testing::Types<
            EvmRevisionConstant<static_cast<evmc_revision>(Is)>...>{};
    }

    using MonadRevisionTypes = decltype(make_monad_revision_types(
        std::make_index_sequence<MONAD_COUNT>{}));

    // Skip over EVMC_REVISION which is EVMC_EXPERIMENTAL
    using EvmRevisionTypes = decltype(make_evm_revision_types(
        std::make_index_sequence<EVMC_MAX_REVISION>{}));

    // Helper to concatenate two ::testing::Types
    template <typename... Ts>
    struct concat_types;

    template <typename... Ts1, typename... Ts2>
    struct concat_types<::testing::Types<Ts1...>, ::testing::Types<Ts2...>>
    {
        using type = ::testing::Types<Ts1..., Ts2...>;
    };

    template <typename... Ts>
    using concat_types_t = typename concat_types<Ts...>::type;

    // Union of MonadRevisionTypes and EvmRevisionTypes
    using MonadEvmRevisionTypes =
        concat_types_t<MonadRevisionTypes, EvmRevisionTypes>;

    struct RevisionTestNameGenerator
    {
        template <typename T>
        static std::string GetName(int)
        {
            if constexpr (std::
                              same_as<typename T::value_type, monad_revision>) {
                return monad_revision_to_string(T::value);
            }
            else {
                return evmc_revision_to_string(T::value);
            }
        }
    };
}

#define DEFINE_MONAD_TRAITS_FIXTURE(FIXTURE_NAME)                              \
    TYPED_TEST_SUITE(                                                          \
        FIXTURE_NAME,                                                          \
        ::detail::MonadRevisionTypes,                                          \
        ::detail::RevisionTestNameGenerator)

#define DEFINE_ETHEREUM_TRAITS_FIXTURE(FIXTURE_NAME)                           \
    TYPED_TEST_SUITE(                                                          \
        FIXTURE_NAME,                                                          \
        ::detail::EvmRevisionTypes,                                            \
        ::detail::RevisionTestNameGenerator)

#define DEFINE_TRAITS_FIXTURE(FIXTURE_NAME)                                    \
    TYPED_TEST_SUITE(                                                          \
        FIXTURE_NAME,                                                          \
        ::detail::MonadEvmRevisionTypes,                                       \
        ::detail::RevisionTestNameGenerator)

template <typename MonadRevisionT>
struct MonadTraitsTest : public ::testing::Test
{
    static constexpr monad_revision REV = MonadRevisionT::value;
    using Trait = monad::MonadTraits<REV>;
};

DEFINE_MONAD_TRAITS_FIXTURE(MonadTraitsTest);

template <typename EvmRevisionT>
struct EvmTraitsTest : public ::testing::Test
{
    static constexpr evmc_revision REV = EvmRevisionT::value;
    using Trait = monad::EvmTraits<REV>;
};

DEFINE_ETHEREUM_TRAITS_FIXTURE(EvmTraitsTest);

template <typename T>
struct TraitsTest : public ::testing::Test
{
    static constexpr auto get_trait()
    {
        if constexpr (std::same_as<typename T::value_type, monad_revision>) {
            return monad::MonadTraits<T::value>{};
        }
        else {
            return monad::EvmTraits<T::value>{};
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
};

std::vector<std::variant<evmc_revision, monad_revision>> monad_evm_revisions()
{
    std::vector<std::variant<evmc_revision, monad_revision>> result;
    for (auto evm_rev = 0; evm_rev < EVMC_MAX_REVISION; ++evm_rev) {
        result.push_back(static_cast<evmc_revision>(evm_rev));
    }
    for (auto monad_rev = 0; monad_rev < MONAD_COUNT; ++monad_rev) {
        result.push_back(static_cast<monad_revision>(monad_rev));
    }
    return result;
}

DEFINE_TRAITS_FIXTURE(TraitsTest);
