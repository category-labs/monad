#pragma once

#include <monad/core/bytes.hpp>

#include <monad/db/assert.h>
#include <monad/db/config.hpp>
#include <monad/db/util.hpp>

#include <monad/state/state_changes.hpp>

#include <rocksdb/db.h>

#include <memory>

MONAD_DB_NAMESPACE_BEGIN

namespace detail
{
    inline void rocks_db_commit_code_to_batch(
        rocksdb::WriteBatch &batch, state::StateChanges const &obj,
        rocksdb::ColumnFamilyHandle *cf)
    {
        for (auto const &[ch, c] : obj.code_changes) {
            auto const res = batch.Put(cf, to_slice(ch), to_slice(c));
            MONAD_ROCKS_ASSERT(res);
        }
    }

    [[nodiscard]] byte_string rocks_db_read_code(
        bytes32_t const &b, std::shared_ptr<rocksdb::DB> db,
        rocksdb::ColumnFamilyHandle *cf);
}

MONAD_DB_NAMESPACE_END
