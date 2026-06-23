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

#include <category/core/assert.h>
#include <category/execution/ethereum/db/make_db.hpp>
#include <category/execution/ethereum/db/state_machine_init.hpp>
#include <category/execution/ethereum/db/util.hpp>
#include <category/mpt/ondisk_db_config.hpp>

#include <memory>
#include <utility>

#ifdef MONAD_HAVE_ROCKSDB
    #include <category/execution/ethereum/db/rocksdb_db.hpp>
#endif

MONAD_NAMESPACE_BEGIN

std::unique_ptr<DbHandle> make_db(DbConfig const &config)
{
#ifdef MONAD_HAVE_ROCKSDB
    if (config.backend == StateBackend::RocksDb) {
        MONAD_ASSERT(!config.rocksdb_dir.empty());
        return std::make_unique<DbHandle>(
            std::make_unique<RocksDbDb>(config.rocksdb_dir));
    }
#endif

    // The only other backend is MonadDB; --state-backend selects it.
    MONAD_ASSERT(config.backend == StateBackend::TrieDb);

    // The on-disk Db ctor reads the persisted state_machine_kind from
    // db_metadata and builds the StateMachine via the registry, so register
    // before constructing it; the in-memory path constructs the SM inline.
    register_ethereum_state_machines();

    auto raw_db =
        config.dbname_paths.empty()
            ? std::make_unique<mpt::Db>(std::make_unique<InMemoryMachine>())
            : std::make_unique<mpt::Db>(mpt::OnDiskDbConfig{
                  .append = true,
                  .compaction = config.compaction,
                  .rewind_to_latest_finalized = true,
                  .rd_buffers = 8192,
                  .wr_buffers = 32,
                  .uring_entries = 128,
                  .sq_thread_cpu = config.sq_thread_cpu,
                  .dbname_paths = config.dbname_paths});

#ifdef MONAD_HAVE_ROCKSDB
    std::unique_ptr<FlatStateMirror> flat_mirror;
    if (config.validate_flat_state_dir.has_value()) {
        flat_mirror = FlatStateMirror::open(*config.validate_flat_state_dir);
    }
    auto triedb = std::make_unique<TrieDb>(
        *raw_db, config.enable_multiblock_cache, std::move(flat_mirror));
#else
    auto triedb =
        std::make_unique<TrieDb>(*raw_db, config.enable_multiblock_cache);
#endif

    return std::make_unique<DbHandle>(std::move(raw_db), std::move(triedb));
}

MONAD_NAMESPACE_END
