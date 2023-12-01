#pragma once

#include <monad/core/byte_string.hpp>
#include <monad/db/assert.h>
#include <monad/db/util.hpp>
#include <monad/trie/config.hpp>
#include <monad/trie/key_buffer.hpp>
#include <monad/trie/util.hpp>

#include <rocksdb/db.h>
#include <rocksdb/options.h>

MONAD_TRIE_NAMESPACE_BEGIN

struct RocksWriter
{
    rocksdb::WriteBatch &batch;
    rocksdb::ColumnFamilyHandle *cf;

    void put(KeyBuffer const &key, byte_string_view value)
    {
        MONAD_DEBUG_ASSERT(cf != nullptr);
        auto const res = batch.Put(
            cf, monad::db::to_slice(key.view()), monad::db::to_slice(value));
        MONAD_ROCKS_ASSERT(res);
    }

    void del(KeyBuffer const &key)
    {
        MONAD_DEBUG_ASSERT(cf != nullptr);
        auto res = batch.Delete(cf, monad::db::to_slice(key.view()));
        MONAD_ROCKS_ASSERT(res);
    }

    void del_prefix(byte_string_view prefix)
    {
        MONAD_DEBUG_ASSERT(prefix.size() == sizeof(Address));

        static constexpr std::array<byte_string::value_type, 34> SENTINEL = {
            65,   0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
            0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
            0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
            0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x00};

        KeyBuffer buf;
        buf.set_prefix(prefix);
        serialize_nibbles(buf, Nibbles{});

        auto end = byte_string{buf.prefix()};
        end += byte_string_view(
            reinterpret_cast<byte_string::value_type const *>(SENTINEL.data()),
            SENTINEL.size());

        auto const res = batch.DeleteRange(
            cf, monad::db::to_slice(buf.view()), monad::db::to_slice(end));
        MONAD_ROCKS_ASSERT(res);
    }
};

MONAD_TRIE_NAMESPACE_END
