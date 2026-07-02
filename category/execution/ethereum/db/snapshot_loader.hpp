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

// Self-guarded: empty unless the RocksDB backend is enabled.
#ifdef MONAD_HAVE_ROCKSDB

    #include <category/core/bytes.hpp>
    #include <category/core/config.hpp>

    #include <cstdint>
    #include <filesystem>

MONAD_NAMESPACE_BEGIN

// F8 offline seed loader. Reads the 256-shard ACCOUNT/STORAGE/CODE/ETH_HEADER
// filesystem snapshot produced by monad_db_dump_snapshot and writes the four
// RocksDB column families: CF_FLAT_STATE (raw Address [+ slot] ->
// account/storage value), CF_CODE (code_hash -> bytecode), CF_TRIE_NODES
// (node_hash -> canonical RLP, built via PartialTrieDb), and CF_META (finalized
// = block, state_root, schema.version).
//
// The shard directories are looked up at `snapshot_dir/block` (the canonical
// dump layout) or, if that is absent, directly under `snapshot_dir` (a snapshot
// whose block level was flattened during transfer). No un-hashing: flat keys
// are re-derived from the raw Address/slot embedded in each record. Asserts the
// converted state_root equals block N's ETH_HEADER stateRoot (the seed gate)
// before writing CF_META. Returns the state_root.
//
// Pure offline tool: no MonadDB runtime/device. Builds the trie incrementally
// on disk, streaming one shard at a time, so peak memory is bounded to a single
// shard rather than the whole state.
bytes32_t seed_rocksdb_from_snapshot(
    std::filesystem::path const &snapshot_dir, uint64_t block,
    std::filesystem::path const &rocksdb_dir);

MONAD_NAMESPACE_END

#endif // MONAD_HAVE_ROCKSDB
