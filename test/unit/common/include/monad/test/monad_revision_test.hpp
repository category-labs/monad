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

    template <typename MonadT, typename EvmT>
    struct MonadAndEvmRevision
    {
        static constexpr monad_revision MONAD_REV = MonadT::value;
        static constexpr evmc_revision EVM_REV = EvmT::value;
    };

    // for a single monad revision generate all monad_revision x evm_revision
    // combinations
    template <monad_revision MRev, std::size_t... Js>
    constexpr auto make_evm_combinations(std::index_sequence<Js...>)
    {
        return ::testing::Types<MonadAndEvmRevision<
            MonadRevisionConstant<MRev>,
            EvmRevisionConstant<static_cast<evmc_revision>(Js)>>...>{};
    }

    // helper to flatten multiple ::testing::Types into one
    template <typename... Ts>
    struct concat_types;

    template <typename... Ts1, typename... Ts2, typename... Rest>
    struct concat_types<
        ::testing::Types<Ts1...>, ::testing::Types<Ts2...>, Rest...>
    {
        using type = typename concat_types<
            ::testing::Types<Ts1..., Ts2...>, Rest...>::type;
    };

    template <typename Ts>
    struct concat_types<Ts>
    {
        using type = Ts;
    };

    // generate ALL supported monad_revision x evm_revision combinations
    template <std::size_t... Is>
    constexpr auto make_all_monad_evm_types(std::index_sequence<Is...>)
    {
        return typename concat_types<decltype(make_evm_combinations<
                                              static_cast<monad_revision>(Is)>(
            std::make_index_sequence<
                monad::MonadTraits<static_cast<monad_revision>(Is)>::evm_rev() +
                1>{}))...>::type{};
    }

    using MonadEvmRevisionTypes = decltype(make_all_monad_evm_types(
        std::make_index_sequence<MONAD_COUNT>{}));

    struct MonadRevisionTestNameGenerator
    {
        template <typename T>
        static std::string GetName(int)
        {
            return std::format(
                "{}-{}",
                monad_revision_to_string(T::MONAD_REV),
                evmc_revision_to_string(T::EVM_REV));
        }
    };
}

template <typename MonadEvmRevisionT>
struct MonadRevisionTest : public ::testing::Test
{
    static constexpr monad_revision MONAD_REV = MonadEvmRevisionT::MONAD_REV;
    using MonadTrait = monad::MonadTraits<MONAD_REV>;
};

TYPED_TEST_SUITE(
    MonadRevisionTest, ::detail::MonadEvmRevisionTypes,
    ::detail::MonadRevisionTestNameGenerator);
