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

#include <category/core/bytes.hpp>
#include <category/core/config.hpp>
#include <category/core/log.hpp>
#include <category/execution/ethereum/state2/state_deltas.hpp>

#include <cstdint>

MONAD_NAMESPACE_BEGIN

// File-backed logger that receives one JSON line per block describing the
// state changes. `nullptr` disables logging. Wired up from main() via
// `create_event_tracer(--state-delta-log <path>)`.
extern quill::Logger *state_delta_logger;

// Emit one JSON line describing every account/storage change in the block,
// plus any newly-introduced contract code. No-op when state_delta_logger is
// null.
//
// The JSON object has the shape:
//
//   {
//     "block": <number>,
//     "block_hash": "0x<32-byte hex>",
//     "parent_hash": "0x<32-byte hex>",
//     "accounts": {
//       "0x<20-byte addr>": {
//         "pre":  { balance, nonce, code_hash, incarnation } | null,
//         "post": { balance, nonce, code_hash, incarnation } | null,
//         "storage": { "0x<32-byte slot>": { "pre": ..., "post": ... }, ... }
//       },
//       ...
//     },
//     "code": { "0x<32-byte code_hash>": "0x<hex bytes>", ... }
//   }
//
// `pre == null` means the account was created in this block; `post == null`
// means it was selfdestructed. Storage entries where pre == post are omitted.
// Keys are sorted within each object for deterministic output.
void log_state_deltas(
    uint64_t block_number, bytes32_t const &block_hash,
    bytes32_t const &parent_hash, StateDeltas const &state, Code const &code);

MONAD_NAMESPACE_END
