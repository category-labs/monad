#pragma once

#include <monad/core/byte_string.hpp>
#include <monad/db/config.hpp>

#include <rocksdb/slice.h>

MONAD_DB_NAMESPACE_BEGIN

namespace detail
{
    constexpr std::string_view CURRENT_DATABASE = "CURRENT";
};

[[nodiscard]] inline rocksdb::Slice to_slice(byte_string_view view)
{
    return {reinterpret_cast<char const *>(view.data()), view.size()};
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
