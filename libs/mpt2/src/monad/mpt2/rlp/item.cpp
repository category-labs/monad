#include <monad/core/likely.h>
#include <monad/mpt2/rlp/item.hpp>
#include <monad/rlp/decode.hpp>
#include <monad/rlp/decode_error.hpp>
#include <monad/rlp/encode2.hpp>

#include <boost/outcome/try.hpp>

MONAD_RLP_NAMESPACE_BEGIN

namespace
{

    Result<RawItem> decode_helper(byte_string_view &enc, size_t depth)
    {
        if (MONAD_UNLIKELY(depth > 128)) {
            return DecodeError::Overflow;
        }
        if (MONAD_UNLIKELY(enc.empty())) {
            return DecodeError::InputTooShort;
        }
        RawItem output;
        if (enc[0] >= 0xc0) {
            BOOST_OUTCOME_TRY(auto payload, rlp::parse_list_metadata(enc));
            RawList list;
            while (!payload.empty()) {
                BOOST_OUTCOME_TRY(
                    auto const elem, decode_helper(payload, depth + 1));
                list.emplace_back(std::move(elem));
            }
            output.value = std::move(list);
        }
        else {
            BOOST_OUTCOME_TRY(auto const string, rlp::decode_string(enc));
            output.value = RawString{string};
        }
        return output;
    }

}

Result<RawItem> decode_item(byte_string_view enc)
{
    BOOST_OUTCOME_TRY(auto const res, decode_helper(enc, 0));
    if (MONAD_UNLIKELY(!enc.empty())) {
        return DecodeError::TypeUnexpected;
    }
    return res;
}

byte_string encode_item(RawItem const &item)
{
    byte_string result;
    if (std::holds_alternative<RawList>(item.value)) {
        auto const &list = std::get<RawList>(item.value);
        byte_string data;
        for (auto const &item : list) {
            data += encode_item(item);
        }
        result = encode_list2(data);
    }
    else {
        auto const &str = std::get<RawString>(item.value);
        result = encode_string2(str);
    }
    return result;
}

MONAD_RLP_NAMESPACE_END
