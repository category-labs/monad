#pragma once

#include <monad/core/byte_string.hpp>
#include <monad/trie/config.hpp>

#include <rocksdb/slice.h>

MONAD_TRIE_NAMESPACE_BEGIN

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

constexpr byte_string_view::value_type
get_nibble(byte_string_view rep, size_t i)
{
    return (i % 2) == 0 ? rep.at(i / 2 + 1) >> 4 : rep.at(i / 2 + 1) & 0x0F;
}

MONAD_TRIE_NAMESPACE_END
