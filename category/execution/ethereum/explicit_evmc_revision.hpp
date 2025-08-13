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

#include <evmc/evmc.h>

#define EXPLICIT_EVMC_REVISION(f)                                              \
    template decltype(f<EVMC_FRONTIER>) f<EVMC_FRONTIER>;                      \
    template decltype(f<EVMC_HOMESTEAD>) f<EVMC_HOMESTEAD>;                    \
    template decltype(f<EVMC_TANGERINE_WHISTLE>) f<EVMC_TANGERINE_WHISTLE>;    \
    template decltype(f<EVMC_SPURIOUS_DRAGON>) f<EVMC_SPURIOUS_DRAGON>;        \
    template decltype(f<EVMC_BYZANTIUM>) f<EVMC_BYZANTIUM>;                    \
    template decltype(f<EVMC_CONSTANTINOPLE>) f<EVMC_CONSTANTINOPLE>;          \
    template decltype(f<EVMC_PETERSBURG>) f<EVMC_PETERSBURG>;                  \
    template decltype(f<EVMC_ISTANBUL>) f<EVMC_ISTANBUL>;                      \
    template decltype(f<EVMC_BERLIN>) f<EVMC_BERLIN>;                          \
    template decltype(f<EVMC_LONDON>) f<EVMC_LONDON>;                          \
    template decltype(f<EVMC_PARIS>) f<EVMC_PARIS>;                            \
    template decltype(f<EVMC_SHANGHAI>) f<EVMC_SHANGHAI>;                      \
    template decltype(f<EVMC_CANCUN>) f<EVMC_CANCUN>;                          \
    template decltype(f<EVMC_PRAGUE>) f<EVMC_PRAGUE>;
