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

#include <category/vm/evm/chain.hpp>

#include <evmc/evmc.h>

#define SWITCH_EVM_CHAIN(f, ...)                                               \
    switch (rev) {                                                             \
    case EVMC_OSAKA:                                                           \
        return f<::monad::EvmChain<EVMC_OSAKA>>(__VA_ARGS__);                  \
    case EVMC_PRAGUE:                                                          \
        return f<::monad::EvmChain<EVMC_PRAGUE>>(__VA_ARGS__);                 \
    case EVMC_CANCUN:                                                          \
        return f<::monad::EvmChain<EVMC_CANCUN>>(__VA_ARGS__);                 \
    case EVMC_SHANGHAI:                                                        \
        return f<::monad::EvmChain<EVMC_SHANGHAI>>(__VA_ARGS__);               \
    case EVMC_PARIS:                                                           \
        return f<::monad::EvmChain<EVMC_PARIS>>(__VA_ARGS__);                  \
    case EVMC_LONDON:                                                          \
        return f<::monad::EvmChain<EVMC_LONDON>>(__VA_ARGS__);                 \
    case EVMC_BERLIN:                                                          \
        return f<::monad::EvmChain<EVMC_BERLIN>>(__VA_ARGS__);                 \
    case EVMC_ISTANBUL:                                                        \
        return f<::monad::EvmChain<EVMC_ISTANBUL>>(__VA_ARGS__);               \
    case EVMC_PETERSBURG:                                                      \
    case EVMC_CONSTANTINOPLE:                                                  \
        return f<::monad::EvmChain<EVMC_PETERSBURG>>(__VA_ARGS__);             \
    case EVMC_BYZANTIUM:                                                       \
        return f<::monad::EvmChain<EVMC_BYZANTIUM>>(__VA_ARGS__);              \
    case EVMC_SPURIOUS_DRAGON:                                                 \
        return f<::monad::EvmChain<EVMC_SPURIOUS_DRAGON>>(__VA_ARGS__);        \
    case EVMC_TANGERINE_WHISTLE:                                               \
        return f<::monad::EvmChain<EVMC_TANGERINE_WHISTLE>>(__VA_ARGS__);      \
    case EVMC_HOMESTEAD:                                                       \
        return f<::monad::EvmChain<EVMC_HOMESTEAD>>(__VA_ARGS__);              \
    case EVMC_FRONTIER:                                                        \
        return f<::monad::EvmChain<EVMC_FRONTIER>>(__VA_ARGS__);               \
    default:                                                                   \
        break;                                                                 \
    }
