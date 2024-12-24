#pragma once

#include <monad/core/byte_string.hpp>
#include <monad/core/result.hpp>
#include <monad/rlp/config.hpp>

#include <variant>
#include <vector>

MONAD_RLP_NAMESPACE_BEGIN

struct RawItem;
using RawString = byte_string;
using RawList = std::vector<RawItem>;

struct RawItem
{
    std::variant<RawString, RawList> value;
};

Result<RawItem> decode_item(byte_string_view enc);
byte_string encode_item(RawItem const &);

MONAD_RLP_NAMESPACE_END
