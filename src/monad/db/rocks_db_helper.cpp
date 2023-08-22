#include <monad/core/byte_string.hpp>
#include <monad/core/bytes.hpp>

#include <monad/db/assert.h>
#include <monad/db/config.hpp>
#include <monad/db/rocks_db_helper.hpp>
#include <monad/db/util.hpp>

#include <monad/state/state_changes.hpp>

#include <rocksdb/db.h>

#include <memory>

MONAD_DB_NAMESPACE_BEGIN

namespace detail
{
    [[nodiscard]] byte_string rocks_db_read_code(
        bytes32_t const &ch, std::shared_ptr<rocksdb::DB> db,
        rocksdb::ColumnFamilyHandle *cf)
    {
        rocksdb::PinnableSlice value;
        auto const res =
            db->Get(rocksdb::ReadOptions{}, cf, to_slice(ch), &value);
        if (res.IsNotFound()) {
            return byte_string{};
        }
        MONAD_ROCKS_ASSERT(res);
        byte_string ret{
            reinterpret_cast<byte_string_view::value_type const *>(
                value.data()),
            value.size()};

        return ret;
    }

}

MONAD_DB_NAMESPACE_END
