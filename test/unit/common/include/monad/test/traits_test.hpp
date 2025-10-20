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
    template <template <auto> class T, std::size_t... Is>
    constexpr auto make_monad_revision_types(std::index_sequence<Is...>)
    {
        return ::testing::Types<T<static_cast<monad_revision>(Is)>...>{};
    }

    template <template <auto> class T, std::size_t... Is>
    constexpr auto make_evm_revision_types(std::index_sequence<Is...>)
    {
        return ::testing::Types<T<static_cast<evmc_revision>(Is)>...>{};
    }
}

template <template <auto> class T>
constexpr auto make_monad_revision_types()
{
    return ::detail::make_monad_revision_types<T>(
        std::make_index_sequence<MONAD_COUNT>{});
}

template <template <auto> class T>
constexpr auto make_evm_revision_types()
{
    // Skip over EVMC_REVISION which is EVMC_EXPERIMENTAL
    return ::detail::make_evm_revision_types<T>(
        std::make_index_sequence<EVMC_MAX_REVISION>{});
}

namespace detail
{
    template <monad_revision rev>
    using MonadRevisionConstant = std::integral_constant<monad_revision, rev>;

    template <evmc_revision rev>
    using EvmRevisionConstant = std::integral_constant<evmc_revision, rev>;

    using MonadRevisionTypes =
        decltype(::make_monad_revision_types<MonadRevisionConstant>());

    using EvmRevisionTypes =
        decltype(::make_evm_revision_types<EvmRevisionConstant>());

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

template <typename MonadRevisionT>
struct MonadTraitsTest : public ::testing::Test
{
    static constexpr monad_revision REV = MonadRevisionT::value;
    using Trait = monad::MonadTraits<REV>;
};

TYPED_TEST_SUITE(
    MonadTraitsTest, ::detail::MonadRevisionTypes,
    ::detail::RevisionTestNameGenerator);

template <typename EvmRevisionT>
struct EvmTraitsTest : public ::testing::Test
{
    static constexpr evmc_revision REV = EvmRevisionT::value;
    using Trait = monad::EvmTraits<REV>;
};

TYPED_TEST_SUITE(
    EvmTraitsTest, ::detail::EvmRevisionTypes,
    ::detail::RevisionTestNameGenerator);

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

TYPED_TEST_SUITE(
    TraitsTest, ::detail::MonadEvmRevisionTypes,
    ::detail::RevisionTestNameGenerator);
