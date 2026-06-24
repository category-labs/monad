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
#include <category/core/byte_string.hpp>
#include <category/statedb/kv_store.hpp>
#include <category/statedb/schema.hpp>

#include <rocksdb/cache.h>
#include <rocksdb/db.h>
#include <rocksdb/filter_policy.h>
#include <rocksdb/iterator.h>
#include <rocksdb/options.h>
#include <rocksdb/slice.h>
#include <rocksdb/snapshot.h>
#include <rocksdb/status.h>
#include <rocksdb/table.h>
#include <rocksdb/write_batch.h>

#include <cstdint>
#include <cstdlib>
#include <memory>
#include <string>

MONAD_NAMESPACE_BEGIN

namespace statedb
{
    namespace
    {
        rocksdb::Slice to_slice(byte_string_view const v) noexcept
        {
            return rocksdb::Slice(
                reinterpret_cast<char const *>(v.data()), v.size());
        }

        byte_string to_bytes(std::string const &s)
        {
            return byte_string{
                reinterpret_cast<unsigned char const *>(s.data()), s.size()};
        }
    }

    namespace
    {
        // CF_TRIE_NODES is keyed by node hash, so root computation does many
        // random point reads with no locality -- a large block cache + bloom
        // filters keep most of the working set (and the trie's hot upper
        // levels) resident instead of hitting the SST. The cache size in MiB is
        // read from the env var below (default 4096); bump it on a big-RAM box.
        std::size_t block_cache_bytes()
        {
            std::size_t mb = 4096; // MONAD_ROCKSDB_BLOCK_CACHE_MB overrides
            if (char const *const env =
                    std::getenv("MONAD_ROCKSDB_BLOCK_CACHE_MB")) {
                char *end = nullptr;
                unsigned long const v = std::strtoul(env, &end, 10);
                if (end != env && v > 0) {
                    mb = static_cast<std::size_t>(v);
                }
            }
            return mb << 20;
        }
    }

    std::unique_ptr<KvStore> KvStore::open(std::filesystem::path const &dir)
    {
        rocksdb::DBOptions db_options;
        db_options.create_if_missing = true;
        db_options.create_missing_column_families = true;
        db_options.max_background_jobs = 6;
        db_options.bytes_per_sync = 1u << 20;

        // One shared block cache + a bloom-filtered, index/filter-pinned table
        // format across all CFs (see block_cache_bytes above).
        rocksdb::BlockBasedTableOptions table_options;
        table_options.block_cache = rocksdb::NewLRUCache(block_cache_bytes());
        table_options.block_size = 16 * 1024;
        table_options.cache_index_and_filter_blocks = true;
        table_options.pin_l0_filter_and_index_blocks_in_cache = true;
        table_options.filter_policy.reset(
            rocksdb::NewBloomFilterPolicy(10, false));
        table_options.format_version = 5;
        auto const table_factory = std::shared_ptr<rocksdb::TableFactory>(
            rocksdb::NewBlockBasedTableFactory(table_options));

        // Compression is left at the RocksDB default: the vendored build may
        // not link LZ4/ZSTD, and an unsupported type fails DB::Open. The speed
        // win here is the block cache + bloom filters, not compression.
        auto cf_options = [&] {
            rocksdb::ColumnFamilyOptions o;
            o.table_factory = table_factory;
            o.level_compaction_dynamic_level_bytes = true;
            o.write_buffer_size = std::size_t{128} << 20;
            return o;
        };

        // RocksDB requires the default column family to be listed explicitly.
        std::vector<rocksdb::ColumnFamilyDescriptor> descriptors;
        descriptors.emplace_back(
            rocksdb::kDefaultColumnFamilyName, cf_options());
        for (std::size_t i = 0; i < NUM_CF; ++i) {
            descriptors.emplace_back(std::string{CF_NAMES[i]}, cf_options());
        }

        std::vector<rocksdb::ColumnFamilyHandle *> handles;
        rocksdb::DB *db = nullptr;
        rocksdb::Status const s = rocksdb::DB::Open(
            db_options, dir.string(), descriptors, &handles, &db);
        MONAD_ASSERT(s.ok());
        MONAD_ASSERT(handles.size() == NUM_CF + 1);

        std::array<rocksdb::ColumnFamilyHandle *, NUM_CF> cf{};
        for (std::size_t i = 0; i < NUM_CF; ++i) {
            cf[i] = handles[i + 1];
        }
        return std::unique_ptr<KvStore>(new KvStore(db, handles[0], cf));
    }

    KvStore::KvStore(
        rocksdb::DB *const db, rocksdb::ColumnFamilyHandle *const default_cf,
        std::array<rocksdb::ColumnFamilyHandle *, NUM_CF> const cf)
        : db_{db}
        , default_cf_{default_cf}
        , cf_{cf}
    {
    }

    KvStore::~KvStore()
    {
        for (auto *const h : cf_) {
            db_->DestroyColumnFamilyHandle(h);
        }
        db_->DestroyColumnFamilyHandle(default_cf_);
        delete db_;
    }

    rocksdb::DB &KvStore::db() const noexcept
    {
        return *db_;
    }

    rocksdb::ColumnFamilyHandle *KvStore::handle(Cf const cf) const noexcept
    {
        return cf_[static_cast<std::size_t>(cf)];
    }

    std::optional<byte_string> KvStore::get(
        Cf const cf, byte_string_view const key,
        rocksdb::Snapshot const *const snapshot) const
    {
        rocksdb::ReadOptions ropts;
        ropts.snapshot = snapshot;
        std::string value;
        rocksdb::Status const s =
            db_->Get(ropts, handle(cf), to_slice(key), &value);
        if (s.IsNotFound()) {
            return std::nullopt;
        }
        MONAD_ASSERT(s.ok());
        return to_bytes(value);
    }

    std::vector<std::optional<byte_string>> KvStore::multi_get(
        Cf const cf, std::span<byte_string_view const> const keys,
        rocksdb::Snapshot const *const snapshot) const
    {
        rocksdb::ReadOptions ropts;
        ropts.snapshot = snapshot;

        std::vector<rocksdb::Slice> slices;
        slices.reserve(keys.size());
        for (byte_string_view const k : keys) {
            slices.push_back(to_slice(k));
        }
        std::vector<rocksdb::ColumnFamilyHandle *> const cfs(
            keys.size(), handle(cf));
        std::vector<std::string> values;
        std::vector<rocksdb::Status> const statuses =
            db_->MultiGet(ropts, cfs, slices, &values);

        std::vector<std::optional<byte_string>> out;
        out.reserve(statuses.size());
        for (std::size_t i = 0; i < statuses.size(); ++i) {
            if (statuses[i].IsNotFound()) {
                out.emplace_back(std::nullopt);
            }
            else {
                MONAD_ASSERT(statuses[i].ok());
                out.emplace_back(to_bytes(values[i]));
            }
        }
        return out;
    }

    void KvStore::put(
        Cf const cf, byte_string_view const key, byte_string_view const value)
    {
        rocksdb::Status const s = db_->Put(
            rocksdb::WriteOptions{},
            handle(cf),
            to_slice(key),
            to_slice(value));
        MONAD_ASSERT(s.ok());
    }

    void KvStore::erase(Cf const cf, byte_string_view const key)
    {
        rocksdb::Status const s =
            db_->Delete(rocksdb::WriteOptions{}, handle(cf), to_slice(key));
        MONAD_ASSERT(s.ok());
    }

    void KvStore::batch_put(
        rocksdb::WriteBatch &batch, Cf const cf, byte_string_view const key,
        byte_string_view const value) const
    {
        rocksdb::Status const s =
            batch.Put(handle(cf), to_slice(key), to_slice(value));
        MONAD_ASSERT(s.ok());
    }

    void KvStore::batch_erase(
        rocksdb::WriteBatch &batch, Cf const cf,
        byte_string_view const key) const
    {
        rocksdb::Status const s = batch.Delete(handle(cf), to_slice(key));
        MONAD_ASSERT(s.ok());
    }

    void KvStore::write(rocksdb::WriteBatch &batch, bool const sync)
    {
        rocksdb::WriteOptions wopts;
        wopts.sync = sync;
        rocksdb::Status const s = db_->Write(wopts, &batch);
        MONAD_ASSERT(s.ok());
    }

    rocksdb::Snapshot const *KvStore::take_snapshot()
    {
        return db_->GetSnapshot();
    }

    void KvStore::release(rocksdb::Snapshot const *const snapshot)
    {
        db_->ReleaseSnapshot(snapshot);
    }

    std::unique_ptr<rocksdb::Iterator> KvStore::new_iterator(
        Cf const cf, rocksdb::Snapshot const *const snapshot) const
    {
        rocksdb::ReadOptions ropts;
        ropts.snapshot = snapshot;
        return std::unique_ptr<rocksdb::Iterator>(
            db_->NewIterator(ropts, handle(cf)));
    }
}

MONAD_NAMESPACE_END
