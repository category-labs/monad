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

#include <category/vm/evm/chain.hpp>

#include <evmc/evmc.h>

#define EXPLICIT_EVM_CHAIN(f)                                                  \
    template decltype(f<::monad::EvmChain<EVMC_FRONTIER>>)                     \
        f<::monad::EvmChain<EVMC_FRONTIER>>;                                   \
    template decltype(f<::monad::EvmChain<EVMC_HOMESTEAD>>)                    \
        f<::monad::EvmChain<EVMC_HOMESTEAD>>;                                  \
    template decltype(f<::monad::EvmChain<EVMC_TANGERINE_WHISTLE>>)            \
        f<::monad::EvmChain<EVMC_TANGERINE_WHISTLE>>;                          \
    template decltype(f<::monad::EvmChain<EVMC_SPURIOUS_DRAGON>>)              \
        f<::monad::EvmChain<EVMC_SPURIOUS_DRAGON>>;                            \
    template decltype(f<::monad::EvmChain<EVMC_BYZANTIUM>>)                    \
        f<::monad::EvmChain<EVMC_BYZANTIUM>>;                                  \
    template decltype(f<::monad::EvmChain<EVMC_CONSTANTINOPLE>>)               \
        f<::monad::EvmChain<EVMC_CONSTANTINOPLE>>;                             \
    template decltype(f<::monad::EvmChain<EVMC_PETERSBURG>>)                   \
        f<::monad::EvmChain<EVMC_PETERSBURG>>;                                 \
    template decltype(f<::monad::EvmChain<EVMC_ISTANBUL>>)                     \
        f<::monad::EvmChain<EVMC_ISTANBUL>>;                                   \
    template decltype(f<::monad::EvmChain<EVMC_BERLIN>>)                       \
        f<::monad::EvmChain<EVMC_BERLIN>>;                                     \
    template decltype(f<::monad::EvmChain<EVMC_LONDON>>)                       \
        f<::monad::EvmChain<EVMC_LONDON>>;                                     \
    template decltype(f<::monad::EvmChain<EVMC_PARIS>>)                        \
        f<::monad::EvmChain<EVMC_PARIS>>;                                      \
    template decltype(f<::monad::EvmChain<EVMC_SHANGHAI>>)                     \
        f<::monad::EvmChain<EVMC_SHANGHAI>>;                                   \
    template decltype(f<::monad::EvmChain<EVMC_CANCUN>>)                       \
        f<::monad::EvmChain<EVMC_CANCUN>>;                                     \
    template decltype(f<::monad::EvmChain<EVMC_PRAGUE>>)                       \
        f<::monad::EvmChain<EVMC_PRAGUE>>;                                     \
    template decltype(f<::monad::EvmChain<EVMC_OSAKA>>)                        \
        f<::monad::EvmChain<EVMC_OSAKA>>;

#define EXPLICIT_EVM_CHAIN_MEMBER_LIST(f, id)                                  \
    template <::monad::Traits traits>                                          \
    constexpr auto id = &f<traits>;                                            \
                                                                               \
    template decltype(id<::monad::EvmChain<EVMC_FRONTIER>>)                    \
        id<::monad::EvmChain<EVMC_FRONTIER>>;                                  \
    template decltype(id<::monad::EvmChain<EVMC_HOMESTEAD>>)                   \
        id<::monad::EvmChain<EVMC_HOMESTEAD>>;                                 \
    template decltype(id<::monad::EvmChain<EVMC_TANGERINE_WHISTLE>>)           \
        id<::monad::EvmChain<EVMC_TANGERINE_WHISTLE>>;                         \
    template decltype(id<::monad::EvmChain<EVMC_SPURIOUS_DRAGON>>)             \
        id<::monad::EvmChain<EVMC_SPURIOUS_DRAGON>>;                           \
    template decltype(id<::monad::EvmChain<EVMC_BYZANTIUM>>)                   \
        id<::monad::EvmChain<EVMC_BYZANTIUM>>;                                 \
    template decltype(id<::monad::EvmChain<EVMC_CONSTANTINOPLE>>)              \
        id<::monad::EvmChain<EVMC_CONSTANTINOPLE>>;                            \
    template decltype(id<::monad::EvmChain<EVMC_PETERSBURG>>)                  \
        id<::monad::EvmChain<EVMC_PETERSBURG>>;                                \
    template decltype(id<::monad::EvmChain<EVMC_ISTANBUL>>)                    \
        id<::monad::EvmChain<EVMC_ISTANBUL>>;                                  \
    template decltype(id<::monad::EvmChain<EVMC_BERLIN>>)                      \
        id<::monad::EvmChain<EVMC_BERLIN>>;                                    \
    template decltype(id<::monad::EvmChain<EVMC_LONDON>>)                      \
        id<::monad::EvmChain<EVMC_LONDON>>;                                    \
    template decltype(id<::monad::EvmChain<EVMC_PARIS>>)                       \
        id<::monad::EvmChain<EVMC_PARIS>>;                                     \
    template decltype(id<::monad::EvmChain<EVMC_SHANGHAI>>)                    \
        id<::monad::EvmChain<EVMC_SHANGHAI>>;                                  \
    template decltype(id<::monad::EvmChain<EVMC_CANCUN>>)                      \
        id<::monad::EvmChain<EVMC_CANCUN>>;                                    \
    template decltype(id<::monad::EvmChain<EVMC_PRAGUE>>)                      \
        id<::monad::EvmChain<EVMC_PRAGUE>>;                                    \
    template decltype(id<::monad::EvmChain<EVMC_OSAKA>>)                       \
        id<::monad::EvmChain<EVMC_OSAKA>>;

#define CONCAT2(a, b) a##b
#define CONCAT(a, b) CONCAT2(a, b)

#define EXPLICIT_EVM_CHAIN_MEMBER(f)                                           \
    EXPLICIT_EVM_CHAIN_MEMBER_LIST(f, CONCAT(_member_fn_ptr_, __COUNTER__))

// NOLINTEND(bugprone-macro-parentheses)
