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

#include <cstdint>

#ifdef __cplusplus
extern "C" {
#endif

struct MonadRunloopWord
{
    uint8_t bytes[32];
};

struct MonadRunloopAddress
{
    uint8_t bytes[20];
};

// Opaque runloop structure:
typedef void MonadRunloop;

// Make a new runloop client
MonadRunloop *monad_runloop_new(
    uint64_t chain_id, char const *ledger_path, char const *db_path);

// Deallocate a runloop client
void monad_runloop_delete(MonadRunloop *);

// Execute and finalize `nblocks` number of blocks.
void monad_runloop_run(MonadRunloop *, uint64_t nblocks);

// Set balance of the account with given address.
void monad_runloop_set_balance(
    MonadRunloop *,
    MonadRunloopAddress const *,
    MonadRunloopWord const *);

// Get balance of the account with given address.
// Balance is stored in `result_balance`
void monad_runloop_get_balance(
    MonadRunloop *,
    MonadRunloopAddress const *,
    MonadRunloopWord *result_balance);

// Store current state root in `result_state_root`.
void monad_runloop_get_state_root(
    MonadRunloop *,
    MonadRunloopWord *result_state_root);

#ifdef __cplusplus
}
#endif
