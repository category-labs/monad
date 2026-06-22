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
#include <category/statedb/schema.hpp>

#include <array>
#include <filesystem>
#include <memory>
#include <optional>
#include <span>
#include <vector>

// Forward-declare the RocksDB types exposed by pointer/reference so this header
// does not force RocksDB includes on every consumer (RocksDB uses the default
// `rocksdb` namespace; the build does not override ROCKSDB_NAMESPACE).
namespace rocksdb
{
    class DB;
    class ColumnFamilyHandle;
    class WriteBatch;
    class Iterator;
    class Snapshot;
}

MONAD_NAMESPACE_BEGIN

namespace statedb
{
    // Thin RAII wrapper over a RocksDB database opened with the four state
    // column families (see schema.hpp). It owns the DB handle plus the per-CF
    // handles and exposes the primitives the RocksDbDb backend will need:
    // get / multi_get / put / erase, atomic cross-CF WriteBatch commit,
    // snapshots, and per-CF iterators. Keys and values are raw bytes. Pruning
    // is not wired (keep-all). Leaf component with no callers yet (F2).
    //
    // Error handling is fail-fast: a missing key reads back as nullopt, but any
    // other RocksDB error aborts the process (suits the replay prototype).
    class KvStore
    {
    public:
        // Open `dir`, creating the database and any missing column families.
        static std::unique_ptr<KvStore> open(std::filesystem::path const &dir);

        ~KvStore();
        KvStore(KvStore const &) = delete;
        KvStore &operator=(KvStore const &) = delete;

        // Reads. A non-null `snapshot` pins a consistent view.
        std::optional<byte_string>
        get(Cf, byte_string_view key,
            rocksdb::Snapshot const *snapshot = nullptr) const;

        // One status per key, in order; a missing key yields nullopt.
        std::vector<std::optional<byte_string>> multi_get(
            Cf, std::span<byte_string_view const> keys,
            rocksdb::Snapshot const *snapshot = nullptr) const;

        // Single-key writes (each its own WAL write).
        void put(Cf, byte_string_view key, byte_string_view value);
        void erase(Cf, byte_string_view key);

        // Atomic, cross-CF batch: stage with batch_*, then commit with write().
        void batch_put(
            rocksdb::WriteBatch &, Cf, byte_string_view key,
            byte_string_view value) const;
        void batch_erase(rocksdb::WriteBatch &, Cf, byte_string_view key) const;
        void write(rocksdb::WriteBatch &, bool sync = true);

        // Snapshots: every take_snapshot() must be paired with a release().
        rocksdb::Snapshot const *take_snapshot();
        void release(rocksdb::Snapshot const *);

        // Forward/seek iterator over one column family (caller-owned).
        std::unique_ptr<rocksdb::Iterator>
        new_iterator(Cf, rocksdb::Snapshot const *snapshot = nullptr) const;

        // Raw handles for advanced paths (e.g. batched MultiGet in F11).
        rocksdb::DB &db() const noexcept;
        rocksdb::ColumnFamilyHandle *handle(Cf) const noexcept;

    private:
        KvStore(
            rocksdb::DB *, rocksdb::ColumnFamilyHandle *default_cf,
            std::array<rocksdb::ColumnFamilyHandle *, NUM_CF>);

        rocksdb::DB *db_;
        rocksdb::ColumnFamilyHandle *default_cf_;
        std::array<rocksdb::ColumnFamilyHandle *, NUM_CF> cf_;
    };
}

MONAD_NAMESPACE_END
