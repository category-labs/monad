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

// F8 offline seed loader. Reads the filesystem snapshot at `snapshot_dir/block`
// (the 256-shard ACCOUNT/STORAGE/CODE/ETH_HEADER format produced by
// monad_db_dump_snapshot) and writes a RocksDB store at `rocksdb_dir`:
//   CF_FLAT_STATE  raw Address [+ incarnation + slot] -> account / storage
//   value CF_CODE        code_hash -> bytecode CF_TRIE_NODES  node_hash ->
//   canonical RLP (built via PartialTrieDb) CF_META        finalized = block,
//   state_root, schema.version
// No un-hashing: flat keys are re-derived from the raw Address/slot embedded in
// each record. Asserts the converted state_root equals block N's ETH_HEADER
// stateRoot (the seed gate) before writing CF_META. Returns the state_root.
//
// Pure offline tool: no MonadDB runtime/device. Holds the converted state in
// memory while building the trie (fine for the prototype/tests; streaming for
// the full mainnet snapshot is a later concern).
bytes32_t seed_rocksdb_from_snapshot(
    std::filesystem::path const &snapshot_dir, uint64_t block,
    std::filesystem::path const &rocksdb_dir);

MONAD_NAMESPACE_END

#endif // MONAD_HAVE_ROCKSDB
