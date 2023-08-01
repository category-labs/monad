#pragma once

#include <monad/core/byte_string.hpp>
#include <monad/db/config.hpp>
#include <monad/execution/config.hpp>

#include <rocksdb/slice.h>

MONAD_EXECUTION_NAMESPACE_BEGIN
struct BoostFiberExecution;
MONAD_EXECUTION_NAMESPACE_END

MONAD_DB_NAMESPACE_BEGIN

namespace detail
{
    template <typename TExecution>
    struct RocksTrieDB;
};
using RocksTrieDB = detail::RocksTrieDB<monad::execution::BoostFiberExecution>;

template <typename TDB>
[[nodiscard]] constexpr std::string_view as_string() noexcept
{
    using namespace std::literals::string_view_literals;
    if constexpr (std::same_as<TDB, db::RocksTrieDB>) {
        return "rockstriedb"sv;
    }
}

[[nodiscard]] inline rocksdb::Slice to_slice(byte_string_view view)
{
    return {reinterpret_cast<const char *>(view.data()), view.size()};
}

[[nodiscard]] inline byte_string_view from_slice(rocksdb::Slice slice)
{
    return {
        reinterpret_cast<byte_string_view::value_type const *>(slice.data()),
        slice.size()};
}

template <size_t N>
static inline rocksdb::Slice to_slice(byte_string_fixed<N> const &s)
{
    return rocksdb::Slice{reinterpret_cast<char const *>(s.data()), s.size()};
}

MONAD_DB_NAMESPACE_END
