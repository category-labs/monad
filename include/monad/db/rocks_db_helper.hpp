#pragma once

#include <monad/core/bytes.hpp>

#include <monad/db/assert.h>
#include <monad/db/concepts.hpp>
#include <monad/db/config.hpp>
#include <monad/db/util.hpp>

#include <monad/state/concepts.hpp>
#include <monad/state/state_changes.hpp>

#include <rocksdb/db.h>

#include <memory>

MONAD_DB_NAMESPACE_BEGIN

namespace detail
{
    void commit_code_to_rocks_db_batch(
        rocksdb::WriteBatch &batch, state::changeset auto const &obj,
        rocksdb::ColumnFamilyHandle *cf)
    {
        for (auto const &[ch, c] : obj.code_changes) {
            auto const res = batch.Put(cf, to_slice(ch), to_slice(c));
            MONAD_ROCKS_ASSERT(res);
        }
    }

    [[nodiscard]] bool rocks_db_contains_impl(
        bytes32_t const &b, std::shared_ptr<rocksdb::DB> db,
        rocksdb::ColumnFamilyHandle *cf);

    [[nodiscard]] byte_string rocks_db_try_find_impl(
        bytes32_t const &b, std::shared_ptr<rocksdb::DB> db,
        rocksdb::ColumnFamilyHandle *cf);
}

MONAD_DB_NAMESPACE_END
