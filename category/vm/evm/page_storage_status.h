// Copyright (C) 2025-26 Category Labs, Inc.
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

#include <stdbool.h>

#ifdef __cplusplus
extern "C"
{
#endif

// In-tree mirror of the fork-only `evmc_page_storage_status` (MIP-8 SSTORE page
// accounting). Converted to the evmc struct only in the test-only
// EvmcHostAdapter.
struct monad_page_storage_status
{
    bool first_page_write;
    bool grew_state;
};

struct evmc_page_storage_status
to_evmc_page_storage_status(struct monad_page_storage_status status);

#ifdef __cplusplus
} // extern "C"
#endif
