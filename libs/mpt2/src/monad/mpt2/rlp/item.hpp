#pragma once

#include <monad/core/byte_string.hpp>
#include <monad/core/result.hpp>
#include <monad/mpt/merkle/node_reference.hpp>
#include <monad/mpt2/proof.hpp>
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

template <typename T>
Result<T> UnwrapItemOrError(rlp::RawItem const &item)
{
    if (MONAD_LIKELY(std::holds_alternative<T>(item.value))) {
        return std::get<T>(item.value);
    }
    return mpt2::ProofError::UnexpectedType;
}

inline bytes32_t to_node_reference(rlp::RawItem node)
{
    bytes32_t h{};
    auto const rlp = rlp::encode_item(node);
    mpt::to_node_reference(rlp, h.bytes);
    return h;
}

inline Result<bytes32_t> to_key(rlp::RawItem node)
{
    if (auto const *data = std::get_if<RawString>(&node.value);
        data != nullptr) {
        byte_string_view const key = *data;
        if (MONAD_UNLIKELY(key.size() > KECCAK256_SIZE)) {
            return mpt2::ProofError::UnexpectedType;
        }
        if (key.size() == KECCAK256_SIZE) {
            return to_bytes(key);
        }
    }
    return to_node_reference(node);
}

MONAD_RLP_NAMESPACE_END
