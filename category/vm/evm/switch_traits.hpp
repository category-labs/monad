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

#include <category/vm/evm/traits.hpp>

#include <evmc/evmc.h>

#define SWITCH_EVM_TRAITS(f, ...)                                              \
    switch (rev) {                                                             \
    case EVMC_OSAKA:                                                           \
        return f<::monad::EvmTraits<EVMC_OSAKA>>(__VA_ARGS__);                 \
    case EVMC_PRAGUE:                                                          \
        return f<::monad::EvmTraits<EVMC_PRAGUE>>(__VA_ARGS__);                \
    case EVMC_CANCUN:                                                          \
        return f<::monad::EvmTraits<EVMC_CANCUN>>(__VA_ARGS__);                \
    case EVMC_SHANGHAI:                                                        \
        return f<::monad::EvmTraits<EVMC_SHANGHAI>>(__VA_ARGS__);              \
    case EVMC_PARIS:                                                           \
        return f<::monad::EvmTraits<EVMC_PARIS>>(__VA_ARGS__);                 \
    case EVMC_LONDON:                                                          \
        return f<::monad::EvmTraits<EVMC_LONDON>>(__VA_ARGS__);                \
    case EVMC_BERLIN:                                                          \
        return f<::monad::EvmTraits<EVMC_BERLIN>>(__VA_ARGS__);                \
    case EVMC_ISTANBUL:                                                        \
        return f<::monad::EvmTraits<EVMC_ISTANBUL>>(__VA_ARGS__);              \
    case EVMC_PETERSBURG:                                                      \
        return f<::monad::EvmTraits<EVMC_PETERSBURG>>(__VA_ARGS__);            \
    case EVMC_CONSTANTINOPLE:                                                  \
        return f<::monad::EvmTraits<EVMC_CONSTANTINOPLE>>(__VA_ARGS__);        \
    case EVMC_BYZANTIUM:                                                       \
        return f<::monad::EvmTraits<EVMC_BYZANTIUM>>(__VA_ARGS__);             \
    case EVMC_SPURIOUS_DRAGON:                                                 \
        return f<::monad::EvmTraits<EVMC_SPURIOUS_DRAGON>>(__VA_ARGS__);       \
    case EVMC_TANGERINE_WHISTLE:                                               \
        return f<::monad::EvmTraits<EVMC_TANGERINE_WHISTLE>>(__VA_ARGS__);     \
    case EVMC_HOMESTEAD:                                                       \
        return f<::monad::EvmTraits<EVMC_HOMESTEAD>>(__VA_ARGS__);             \
    case EVMC_FRONTIER:                                                        \
        return f<::monad::EvmTraits<EVMC_FRONTIER>>(__VA_ARGS__);              \
    default:                                                                   \
        break;                                                                 \
    }

#define SWITCH_MONAD_TRAITS(f, ...)                                            \
    switch (rev) {                                                             \
    case MONAD_ZERO:                                                           \
        return f<::monad::MonadTraits<MONAD_ZERO>>(__VA_ARGS__);               \
    case MONAD_ONE:                                                            \
        return f<::monad::MonadTraits<MONAD_ONE>>(__VA_ARGS__);                \
    case MONAD_TWO:                                                            \
        return f<::monad::MonadTraits<MONAD_TWO>>(__VA_ARGS__);                \
    case MONAD_THREE:                                                          \
        return f<::monad::MonadTraits<MONAD_THREE>>(__VA_ARGS__);              \
    case MONAD_FOUR:                                                           \
        return f<::monad::MonadTraits<MONAD_FOUR>>(__VA_ARGS__);               \
    case MONAD_FIVE:                                                           \
        return f<::monad::MonadTraits<MONAD_FIVE>>(__VA_ARGS__);               \
    case MONAD_SIX:                                                            \
        return f<::monad::MonadTraits<MONAD_SIX>>(__VA_ARGS__);                \
    case MONAD_NEXT:                                                           \
        return f<::monad::MonadTraits<MONAD_NEXT>>(__VA_ARGS__);               \
    default:                                                                   \
        break;                                                                 \
    }

// NOLINTEND(bugprone-macro-parentheses)
