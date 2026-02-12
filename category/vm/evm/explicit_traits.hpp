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

// NOLINTBEGIN(bugprone-macro-parentheses)

#include <category/core/concat.h>
#include <category/vm/evm/traits.hpp>

#include <evmc/evmc.h>

// Template free functions

#define EXPLICIT_EVM_TRAITS(f)                                                 \
    template decltype(f<::monad::EvmTraits<EVMC_HOMESTEAD>>)                   \
        f<::monad::EvmTraits<EVMC_HOMESTEAD>>;                                 \
    template decltype(f<::monad::EvmTraits<EVMC_TANGERINE_WHISTLE>>)           \
        f<::monad::EvmTraits<EVMC_TANGERINE_WHISTLE>>;                         \
    template decltype(f<::monad::EvmTraits<EVMC_SPURIOUS_DRAGON>>)             \
        f<::monad::EvmTraits<EVMC_SPURIOUS_DRAGON>>;                           \
    template decltype(f<::monad::EvmTraits<EVMC_BYZANTIUM>>)                   \
        f<::monad::EvmTraits<EVMC_BYZANTIUM>>;                                 \
    template decltype(f<::monad::EvmTraits<EVMC_CONSTANTINOPLE>>)              \
        f<::monad::EvmTraits<EVMC_CONSTANTINOPLE>>;                            \
    template decltype(f<::monad::EvmTraits<EVMC_PETERSBURG>>)                  \
        f<::monad::EvmTraits<EVMC_PETERSBURG>>;                                \
    template decltype(f<::monad::EvmTraits<EVMC_ISTANBUL>>)                    \
        f<::monad::EvmTraits<EVMC_ISTANBUL>>;                                  \
    template decltype(f<::monad::EvmTraits<EVMC_BERLIN>>)                      \
        f<::monad::EvmTraits<EVMC_BERLIN>>;                                    \
    template decltype(f<::monad::EvmTraits<EVMC_LONDON>>)                      \
        f<::monad::EvmTraits<EVMC_LONDON>>;                                    \
    template decltype(f<::monad::EvmTraits<EVMC_PARIS>>)                       \
        f<::monad::EvmTraits<EVMC_PARIS>>;                                     \
    template decltype(f<::monad::EvmTraits<EVMC_SHANGHAI>>)                    \
        f<::monad::EvmTraits<EVMC_SHANGHAI>>;                                  \
    template decltype(f<::monad::EvmTraits<EVMC_CANCUN>>)                      \
        f<::monad::EvmTraits<EVMC_CANCUN>>;                                    \
    template decltype(f<::monad::EvmTraits<EVMC_PRAGUE>>)                      \
        f<::monad::EvmTraits<EVMC_PRAGUE>>;                                    \
    template decltype(f<::monad::EvmTraits<EVMC_OSAKA>>)                       \
        f<::monad::EvmTraits<EVMC_OSAKA>>;

#define EXPLICIT_MONAD_TRAITS(f)                                               \
    template decltype(f<::monad::MonadTraits<MONAD_ZERO>>)                     \
        f<::monad::MonadTraits<MONAD_ZERO>>;                                   \
    template decltype(f<::monad::MonadTraits<MONAD_ONE>>)                      \
        f<::monad::MonadTraits<MONAD_ONE>>;                                    \
    template decltype(f<::monad::MonadTraits<MONAD_TWO>>)                      \
        f<::monad::MonadTraits<MONAD_TWO>>;                                    \
    template decltype(f<::monad::MonadTraits<MONAD_THREE>>)                    \
        f<::monad::MonadTraits<MONAD_THREE>>;                                  \
    template decltype(f<::monad::MonadTraits<MONAD_FOUR>>)                     \
        f<::monad::MonadTraits<MONAD_FOUR>>;                                   \
    template decltype(f<::monad::MonadTraits<MONAD_FIVE>>)                     \
        f<::monad::MonadTraits<MONAD_FIVE>>;                                   \
    template decltype(f<::monad::MonadTraits<MONAD_SIX>>)                      \
        f<::monad::MonadTraits<MONAD_SIX>>;                                    \
    template decltype(f<::monad::MonadTraits<MONAD_SEVEN>>)                    \
        f<::monad::MonadTraits<MONAD_SEVEN>>;                                  \
    template decltype(f<::monad::MonadTraits<MONAD_EIGHT>>)                    \
        f<::monad::MonadTraits<MONAD_EIGHT>>;                                  \
    template decltype(f<::monad::MonadTraits<MONAD_NEXT>>)                     \
        f<::monad::MonadTraits<MONAD_NEXT>>;

#define EXPLICIT_TRAITS(f)                                                     \
    EXPLICIT_EVM_TRAITS(f)                                                     \
    EXPLICIT_MONAD_TRAITS(f)

// Template classes

#define EXPLICIT_EVM_TRAITS_CLASS(c)                                           \
    template class c<::monad::EvmTraits<EVMC_HOMESTEAD>>;                      \
    template class c<::monad::EvmTraits<EVMC_TANGERINE_WHISTLE>>;              \
    template class c<::monad::EvmTraits<EVMC_SPURIOUS_DRAGON>>;                \
    template class c<::monad::EvmTraits<EVMC_BYZANTIUM>>;                      \
    template class c<::monad::EvmTraits<EVMC_CONSTANTINOPLE>>;                 \
    template class c<::monad::EvmTraits<EVMC_PETERSBURG>>;                     \
    template class c<::monad::EvmTraits<EVMC_ISTANBUL>>;                       \
    template class c<::monad::EvmTraits<EVMC_BERLIN>>;                         \
    template class c<::monad::EvmTraits<EVMC_LONDON>>;                         \
    template class c<::monad::EvmTraits<EVMC_PARIS>>;                          \
    template class c<::monad::EvmTraits<EVMC_SHANGHAI>>;                       \
    template class c<::monad::EvmTraits<EVMC_CANCUN>>;                         \
    template class c<::monad::EvmTraits<EVMC_PRAGUE>>;                         \
    template class c<::monad::EvmTraits<EVMC_OSAKA>>;

#define EXPLICIT_MONAD_TRAITS_CLASS(c)                                         \
    template class c<::monad::MonadTraits<MONAD_ZERO>>;                        \
    template class c<::monad::MonadTraits<MONAD_ONE>>;                         \
    template class c<::monad::MonadTraits<MONAD_TWO>>;                         \
    template class c<::monad::MonadTraits<MONAD_THREE>>;                       \
    template class c<::monad::MonadTraits<MONAD_FOUR>>;                        \
    template class c<::monad::MonadTraits<MONAD_FIVE>>;                        \
    template class c<::monad::MonadTraits<MONAD_SIX>>;                         \
    template class c<::monad::MonadTraits<MONAD_SEVEN>>;                       \
    template class c<::monad::MonadTraits<MONAD_EIGHT>>;                       \
    template class c<::monad::MonadTraits<MONAD_NEXT>>;

#define EXPLICIT_TRAITS_CLASS(c)                                               \
    EXPLICIT_EVM_TRAITS_CLASS(c)                                               \
    EXPLICIT_MONAD_TRAITS_CLASS(c)

#define EXPLICIT_MONAD_TRAITS_STRUCT(c)                                        \
    template struct c<::monad::MonadTraits<MONAD_ZERO>>;                       \
    template struct c<::monad::MonadTraits<MONAD_ONE>>;                        \
    template struct c<::monad::MonadTraits<MONAD_TWO>>;                        \
    template struct c<::monad::MonadTraits<MONAD_THREE>>;                      \
    template struct c<::monad::MonadTraits<MONAD_FOUR>>;                       \
    template struct c<::monad::MonadTraits<MONAD_FIVE>>;                       \
    template struct c<::monad::MonadTraits<MONAD_SIX>>;                        \
    template struct c<::monad::MonadTraits<MONAD_SEVEN>>;                      \
    template struct c<::monad::MonadTraits<MONAD_EIGHT>>;                      \
    template struct c<::monad::MonadTraits<MONAD_NEXT>>;

// Template member functions

#define EXPLICIT_TRAITS_MEMBER_HEADER(f, id)                                   \
    template <::monad::Traits traits>                                          \
    constexpr auto id = &f<traits>;

#define EXPLICIT_EVM_TRAITS_MEMBER_LIST(f, id)                                 \
    template decltype(id<::monad::EvmTraits<EVMC_HOMESTEAD>>)                  \
        id<::monad::EvmTraits<EVMC_HOMESTEAD>>;                                \
    template decltype(id<::monad::EvmTraits<EVMC_TANGERINE_WHISTLE>>)          \
        id<::monad::EvmTraits<EVMC_TANGERINE_WHISTLE>>;                        \
    template decltype(id<::monad::EvmTraits<EVMC_SPURIOUS_DRAGON>>)            \
        id<::monad::EvmTraits<EVMC_SPURIOUS_DRAGON>>;                          \
    template decltype(id<::monad::EvmTraits<EVMC_BYZANTIUM>>)                  \
        id<::monad::EvmTraits<EVMC_BYZANTIUM>>;                                \
    template decltype(id<::monad::EvmTraits<EVMC_CONSTANTINOPLE>>)             \
        id<::monad::EvmTraits<EVMC_CONSTANTINOPLE>>;                           \
    template decltype(id<::monad::EvmTraits<EVMC_PETERSBURG>>)                 \
        id<::monad::EvmTraits<EVMC_PETERSBURG>>;                               \
    template decltype(id<::monad::EvmTraits<EVMC_ISTANBUL>>)                   \
        id<::monad::EvmTraits<EVMC_ISTANBUL>>;                                 \
    template decltype(id<::monad::EvmTraits<EVMC_BERLIN>>)                     \
        id<::monad::EvmTraits<EVMC_BERLIN>>;                                   \
    template decltype(id<::monad::EvmTraits<EVMC_LONDON>>)                     \
        id<::monad::EvmTraits<EVMC_LONDON>>;                                   \
    template decltype(id<::monad::EvmTraits<EVMC_PARIS>>)                      \
        id<::monad::EvmTraits<EVMC_PARIS>>;                                    \
    template decltype(id<::monad::EvmTraits<EVMC_SHANGHAI>>)                   \
        id<::monad::EvmTraits<EVMC_SHANGHAI>>;                                 \
    template decltype(id<::monad::EvmTraits<EVMC_CANCUN>>)                     \
        id<::monad::EvmTraits<EVMC_CANCUN>>;                                   \
    template decltype(id<::monad::EvmTraits<EVMC_PRAGUE>>)                     \
        id<::monad::EvmTraits<EVMC_PRAGUE>>;                                   \
    template decltype(id<::monad::EvmTraits<EVMC_OSAKA>>)                      \
        id<::monad::EvmTraits<EVMC_OSAKA>>;

#define EXPLICIT_EVM_TRAITS_MEMBER_HELPER(f, id)                               \
    EXPLICIT_TRAITS_MEMBER_HEADER(f, id)                                       \
    EXPLICIT_EVM_TRAITS_MEMBER_LIST(f, id)

#define EXPLICIT_EVM_TRAITS_MEMBER(f)                                          \
    EXPLICIT_EVM_TRAITS_MEMBER_HELPER(                                         \
        f, MONAD_CORE_CONCAT(_member_fn_ptr_, __COUNTER__))

#define EXPLICIT_MONAD_TRAITS_MEMBER_LIST(f, id)                               \
    template decltype(id<::monad::MonadTraits<MONAD_ZERO>>)                    \
        id<::monad::MonadTraits<MONAD_ZERO>>;                                  \
    template decltype(id<::monad::MonadTraits<MONAD_ONE>>)                     \
        id<::monad::MonadTraits<MONAD_ONE>>;                                   \
    template decltype(id<::monad::MonadTraits<MONAD_TWO>>)                     \
        id<::monad::MonadTraits<MONAD_TWO>>;                                   \
    template decltype(id<::monad::MonadTraits<MONAD_THREE>>)                   \
        id<::monad::MonadTraits<MONAD_THREE>>;                                 \
    template decltype(id<::monad::MonadTraits<MONAD_FOUR>>)                    \
        id<::monad::MonadTraits<MONAD_FOUR>>;                                  \
    template decltype(id<::monad::MonadTraits<MONAD_FIVE>>)                    \
        id<::monad::MonadTraits<MONAD_FIVE>>;                                  \
    template decltype(id<::monad::MonadTraits<MONAD_SIX>>)                     \
        id<::monad::MonadTraits<MONAD_SIX>>;                                   \
    template decltype(id<::monad::MonadTraits<MONAD_SEVEN>>)                   \
        id<::monad::MonadTraits<MONAD_SEVEN>>;                                 \
    template decltype(id<::monad::MonadTraits<MONAD_EIGHT>>)                   \
        id<::monad::MonadTraits<MONAD_EIGHT>>;                                 \
    template decltype(id<::monad::MonadTraits<MONAD_NEXT>>)                    \
        id<::monad::MonadTraits<MONAD_NEXT>>;

#define EXPLICIT_MONAD_TRAITS_MEMBER_HELPER(f, id)                             \
    EXPLICIT_TRAITS_MEMBER_HEADER(f, id)                                       \
    EXPLICIT_MONAD_TRAITS_MEMBER_LIST(f, id)

#define EXPLICIT_MONAD_TRAITS_MEMBER(f)                                        \
    EXPLICIT_MONAD_TRAITS_MEMBER_HELPER(                                       \
        f, MONAD_CORE_CONCAT(_member_fn_ptr_, __COUNTER__))

#define EXPLICIT_TRAITS_MEMBER_HELPER(f, id)                                   \
    EXPLICIT_TRAITS_MEMBER_HEADER(f, id)                                       \
    EXPLICIT_EVM_TRAITS_MEMBER_LIST(f, id)                                     \
    EXPLICIT_MONAD_TRAITS_MEMBER_LIST(f, id)

#define EXPLICIT_TRAITS_MEMBER(f)                                              \
    EXPLICIT_TRAITS_MEMBER_HELPER(                                             \
        f, MONAD_CORE_CONCAT(_member_fn_ptr_, __COUNTER__))

// NOLINTEND(bugprone-macro-parentheses)
