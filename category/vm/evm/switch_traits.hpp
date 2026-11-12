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

#define SWITCH_EVM_TRAITS(f, ...)                                              \
    switch (rev) {                                                             \
    case ::monad::EvmRevision::Amsterdam:                                      \
        return f<::monad::EvmTraits<::monad::EvmRevision::Amsterdam>>(         \
            __VA_ARGS__);                                                      \
    case ::monad::EvmRevision::Osaka:                                          \
        return f<::monad::EvmTraits<::monad::EvmRevision::Osaka>>(             \
            __VA_ARGS__);                                                      \
    case ::monad::EvmRevision::Prague:                                         \
        return f<::monad::EvmTraits<::monad::EvmRevision::Prague>>(            \
            __VA_ARGS__);                                                      \
    case ::monad::EvmRevision::Cancun:                                         \
        return f<::monad::EvmTraits<::monad::EvmRevision::Cancun>>(            \
            __VA_ARGS__);                                                      \
    case ::monad::EvmRevision::Shanghai:                                       \
        return f<::monad::EvmTraits<::monad::EvmRevision::Shanghai>>(          \
            __VA_ARGS__);                                                      \
    case ::monad::EvmRevision::Paris:                                          \
        return f<::monad::EvmTraits<::monad::EvmRevision::Paris>>(             \
            __VA_ARGS__);                                                      \
    case ::monad::EvmRevision::London:                                         \
        return f<::monad::EvmTraits<::monad::EvmRevision::London>>(            \
            __VA_ARGS__);                                                      \
    case ::monad::EvmRevision::Berlin:                                         \
        return f<::monad::EvmTraits<::monad::EvmRevision::Berlin>>(            \
            __VA_ARGS__);                                                      \
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
    case MONAD_SEVEN:                                                          \
        return f<::monad::MonadTraits<MONAD_SEVEN>>(__VA_ARGS__);              \
    case MONAD_EIGHT:                                                          \
        return f<::monad::MonadTraits<MONAD_EIGHT>>(__VA_ARGS__);              \
    case MONAD_NINE:                                                           \
        return f<::monad::MonadTraits<MONAD_NINE>>(__VA_ARGS__);               \
    case MONAD_TEN:                                                            \
        return f<::monad::MonadTraits<MONAD_TEN>>(__VA_ARGS__);                \
    case MONAD_NEXT:                                                           \
        return f<::monad::MonadTraits<MONAD_NEXT>>(__VA_ARGS__);               \
    }

// NOLINTEND(bugprone-macro-parentheses)
