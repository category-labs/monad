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

#include <category/core/assert.h>
#include <category/core/config.hpp>
#include <category/execution/ethereum/db/db.hpp>
#include <category/execution/ethereum/db/trie_db.hpp>
#include <category/mpt/db.hpp>

#include <filesystem>
#include <memory>
#include <optional>
#include <vector>

MONAD_NAMESPACE_BEGIN

enum class StateBackend
{
    TrieDb,
    RocksDb, // requires MONAD_ENABLE_ROCKSDB at build time
};

// Backend-neutral construction parameters for the replay/commit path. Mirrors
// what cmd/monad builds today so StateBackend::TrieDb reproduces it exactly.
struct DbConfig
{
    StateBackend backend{StateBackend::TrieDb};
    std::vector<std::filesystem::path> dbname_paths{}; // empty => in-memory
    bool compaction{true};
    bool enable_multiblock_cache{true};
    std::optional<unsigned> sq_thread_cpu{};
    // F5 (requires MONAD_ENABLE_ROCKSDB): when set, MonadDB also mirrors state
    // into a flat RocksDB store at this directory and asserts flat==trie on
    // reads (validating shadow, replay-only). Empty => disabled.
    std::optional<std::filesystem::path> validate_flat_state_dir{};
    // F9 (StateBackend::RocksDb): the RocksDB store directory to open (a store
    // produced by the F8 seed loader). Ignored for the TrieDb backend.
    std::filesystem::path rocksdb_dir{};
};

// Owns the storage engine plus the monad::Db facade used by the replay/commit
// path. Callers that still need the concrete MonadDB engine -- runloop_monad
// (mpt::Db&), statesync (TrieDb*), and the snapshot/RODb paths -- reach
// raw_db()/triedb() directly; those paths are MonadDB-only and assert if used
// with a non-TrieDb backend. --state-backend selects MonadDB (TrieDb) or
// RocksDb (RocksDbDb). A bare unique_ptr<monad::Db> would hide
// raw_db()/triedb(), which the MonadDB paths require, so the factory hands back
// this owning bundle instead.
class DbHandle
{
public:
    // MonadDB (TrieDb) backend.
    DbHandle(std::unique_ptr<mpt::Db> raw_db, std::unique_ptr<TrieDb> triedb)
        : raw_db_{std::move(raw_db)}
        , triedb_{std::move(triedb)}
    {
    }

    // RocksDb (or any non-TrieDb) backend: only db() is available.
    explicit DbHandle(std::unique_ptr<Db> db)
        : generic_db_{std::move(db)}
    {
    }

    // The backend-neutral injection point.
    Db &db() noexcept
    {
        return triedb_ ? static_cast<Db &>(*triedb_) : *generic_db_;
    }

    // The concrete MonadDB engine (set only for the TrieDb backend).
    mpt::Db &raw_db() noexcept
    {
        MONAD_ASSERT(raw_db_);
        return *raw_db_;
    }

    TrieDb &triedb() noexcept
    {
        MONAD_ASSERT(triedb_);
        return *triedb_;
    }

private:
    std::unique_ptr<mpt::Db> raw_db_;
    std::unique_ptr<TrieDb> triedb_;
    std::unique_ptr<Db> generic_db_;
};

std::unique_ptr<DbHandle> make_db(DbConfig const &);

MONAD_NAMESPACE_END
