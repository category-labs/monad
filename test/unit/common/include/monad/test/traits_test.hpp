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

    // This code was generated using ChatGPT 5
    template <evmc_revision Since, std::size_t... Is>
    constexpr auto make_evm_revision_types(std::index_sequence<Is...>)
    {
        constexpr auto filtered = [] {
            std::array<std::size_t, sizeof...(Is)> result{};
            std::size_t count = 0;

            (
                [&] {
                    constexpr auto evm_rev = static_cast<evmc_revision>(Is);
                    if (evm_rev >= Since) {
                        result[count++] = Is;
                    }
                }(),
                ...);

            return std::pair{result, count};
        }();

        return [&]<std::size_t... Js>(std::index_sequence<Js...>) {
            return ::testing::Types<EvmRevisionConstant<
                static_cast<evmc_revision>(filtered.first[Js])>...>{};
        }(std::make_index_sequence<filtered.second>{});
    }

    template <evmc_revision Since, std::size_t... Is>
    constexpr auto make_monad_revision_types(std::index_sequence<Is...>)
    {
        constexpr auto filtered = [] {
            std::array<std::size_t, sizeof...(Is)> result{};
            std::size_t count = 0;

            (
                [&] {
                    constexpr auto monad_rev = static_cast<monad_revision>(Is);
                    constexpr auto evm_rev =
                        monad::MonadTraits<monad_rev>::evm_rev();
                    if (evm_rev >= Since) {
                        result[count++] = Is;
                    }
                }(),
                ...);

            return std::pair{result, count};
        }();

        // Now expand over the filtered indices
        return [&]<std::size_t... Js>(std::index_sequence<Js...>) {
            return ::testing::Types<MonadRevisionConstant<
                static_cast<monad_revision>(filtered.first[Js])>...>{};
        }(std::make_index_sequence<filtered.second>{});
    }

    using MonadRevisionTypes = decltype(make_monad_revision_types(
        std::make_index_sequence<MONAD_COUNT>{}));

    template <evmc_revision Since>
    using MonadRevisionTypesSince = decltype(make_monad_revision_types<Since>(
        std::make_index_sequence<MONAD_COUNT>{}));

    // Skip over EVMC_REVISION which is EVMC_EXPERIMENTAL
    using EvmRevisionTypes = decltype(make_evm_revision_types(
        std::make_index_sequence<EVMC_MAX_REVISION>{}));

    template <evmc_revision Since>
    using EvmRevisionTypesSince = decltype(make_evm_revision_types<Since>(
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

    template <evmc_revision Since>
    using MonadEvmRevisionTypesSince = concat_types_t<
        MonadRevisionTypesSince<Since>, EvmRevisionTypesSince<Since>>;

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
