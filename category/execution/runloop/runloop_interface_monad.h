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
extern "C"
{
#endif

struct MonadRunloopWord
{
    uint8_t bytes[32];
};

// Opaque runloop structure:
typedef void MonadRunloop;

// Make a new runloop client on the EEST chain (EestNet). The genesis
// allocation (the EEST fixture's `pre` state) is supplied as a JSON
// document: {"<hex address>": {"wei_balance": "<dec|hex>",
// "nonce": "<hex>", "code": "0x..", "storage": {"0x..": "0x.."}}, ...}.
// The genesis block (the fixture's `genesisRLP`) is supplied as a hex
// encoded RLP block, so block 1's parent hash matches the fixture.
// Both are loaded only when the database is freshly created.
// The revision schedule (derived from the fixture's `network`) is a
// comma separated list of "<monad_revision number>:<from timestamp>"
// entries in ascending timestamp order, e.g. "9:0" for a plain
// MONAD_NINE fixture or "8:0,9:15000" for a transition fixture.
MonadRunloop *monad_runloop_new_eest(
    char const *ledger_path, char const *db_path,
    char const *genesis_alloc_json, char const *genesis_block_rlp_hex,
    char const *revision_schedule);

// Deallocate a runloop client
void monad_runloop_delete(MonadRunloop *);

// Execute and finalize `nblocks` number of blocks.
void monad_runloop_run(MonadRunloop *, uint64_t nblocks);

// Store current state root in `result_state_root`.
void monad_runloop_get_state_root(
    MonadRunloop *, MonadRunloopWord *result_state_root);

// Dump the current state of the database as a JSON string. The result
// must be released with monad_runloop_free_string.
char *monad_runloop_dump_json(MonadRunloop *);

// Free a string returned by this interface.
void monad_runloop_free_string(char *);

#ifdef __cplusplus
}
#endif
