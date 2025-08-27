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
