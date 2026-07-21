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

#include <category/core/byte_string.hpp>
#include <category/core/config.hpp>
#include <category/core/keccak.hpp>
#include <category/execution/ethereum/db/db_snapshot.h>
#include <category/mpt/update.hpp>

#include <ankerl/unordered_dense.h>

#include <cstdint>
#include <deque>
#include <memory>

MONAD_NAMESPACE_BEGIN

// Self-contained, DB-free result of prepping one shard. Never moved by value:
// UpdateList is an intrusive slist over the Update objects held in
// account_updates / update_alloc, whose addresses must stay fixed until the
// consumer's db.upsert consumes them. Always passed by unique_ptr.
struct PreparedShard
{
    uint64_t shard{0};
    // Raw file contents the Update.value views point into. Populated only on
    // the file (parallel) path; the buffer path leaves these empty and the
    // caller owns the backing memory for the call's duration.
    byte_string account_bytes;
    byte_string storage_bytes;
    byte_string code_bytes;
    // Backing storage the Update views point into.
    std::deque<hash256> hash_alloc;
    std::deque<byte_string> bytes_alloc;
    std::deque<mpt::Update> update_alloc;
    ankerl::unordered_dense::segmented_map<uint64_t, mpt::Update>
        account_updates;
    mpt::UpdateList state_updates;
    mpt::UpdateList code_updates;
    byte_string eth_header; // owned copy (small), empty if none

    PreparedShard() = default;
    PreparedShard(PreparedShard const &) = delete;
    PreparedShard &operator=(PreparedShard const &) = delete;
};

MONAD_NAMESPACE_END

// Pure-CPU prep of one shard from decoded input views into an already-built
// PreparedShard: RLP decode + keccak256 key derivation + UpdateList build
// (including page-mode page assembly when page_encoded). No Db access. The
// input views must stay valid until the shard's commit_prepared returns; the
// caller keeps them alive either in ps (file path, via account_bytes etc.) or
// externally (C-API buffer path).
void fill_prepared_shard(
    monad::PreparedShard &ps, uint64_t shard, uint64_t block, bool page_encoded,
    monad::byte_string_view eth_header, monad::byte_string_view account,
    monad::byte_string_view storage, monad::byte_string_view code);

// Consumer-side: wrap the shard's updates into the finalized/{state,code}
// tree, upsert into the loader's Db (threading the root), and stash the header.
// Frees the PreparedShard (and its mmaps) once the upsert has copied the
// values out.
void commit_prepared(
    monad_db_snapshot_loader *loader, std::unique_ptr<monad::PreparedShard> ps);

// Whether the loader's target timeline is page-encoded. Const query on the Db's
// state machine kind; safe to read once on the consumer thread before workers
// run.
bool snapshot_loader_page_encoded(monad_db_snapshot_loader const *loader);
