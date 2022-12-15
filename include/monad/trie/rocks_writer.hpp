#pragma once

#include "evmc/evmc.hpp"
#include <monad/core/byte_string.hpp>

#include <monad/trie/assert.h>
#include <monad/trie/config.hpp>
#include <monad/trie/key_buffer.hpp>
#include <monad/trie/util.hpp>
#include <monad/trie/writer.hpp>

#include <rocksdb/db.h>
#include <rocksdb/options.h>

MONAD_TRIE_NAMESPACE_BEGIN

struct RocksWriter
{
    std::shared_ptr<rocksdb::DB> const db;
    rocksdb::WriteBatch batch;
    std::array<rocksdb::ColumnFamilyHandle *, 4> const cfs;

    void put(WriterColumn col, KeyBuffer const &key, byte_string_view value)
    {
        assert(
            (col == WriterColumn::ACCOUNT_ALL ||
             col == WriterColumn::ACCOUNT_LEAVES) ||
            key.view().size() > sizeof(address_t));

        auto *cf = cfs[static_cast<uint8_t>(col)];
        assert(cf);
        auto const res = batch.Put(cf, to_slice(key.view()), to_slice(value));
        MONAD_ROCKS_ASSERT(res);
    }

    void del(WriterColumn col, KeyBuffer const &key)
    {
        assert(
            (col == WriterColumn::ACCOUNT_ALL ||
             col == WriterColumn::ACCOUNT_LEAVES) ||
            key.view().size() > sizeof(address_t));

        auto *cf = cfs[static_cast<uint8_t>(col)];
        assert(cf);
        auto res = batch.Delete(cf, to_slice(key.view()));
        MONAD_ROCKS_ASSERT(res);
    }

    void write()
    {
        auto const res = db->Write(rocksdb::WriteOptions{}, &batch);
        MONAD_ROCKS_ASSERT(res);
        batch.Clear();
    }
};

MONAD_TRIE_NAMESPACE_END
