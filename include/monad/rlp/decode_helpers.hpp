#pragma once

#include <monad/rlp/config.hpp>
#include <monad/rlp/decode.hpp>
#include <monad/rlp/decode_error.hpp>
#include <monad/rlp/util.hpp>

#include <monad/core/account.hpp>
#include <monad/core/address.hpp>
#include <monad/core/block.hpp>
#include <monad/core/byte_string.hpp>
#include <monad/core/receipt.hpp>
#include <monad/core/signature.hpp>
#include <monad/core/transaction.hpp>
#include <monad/core/withdrawal.hpp>

#include <boost/outcome/try.hpp>

#include <vector>

MONAD_RLP_NAMESPACE_BEGIN

template <unsigned_integral T>
constexpr DecodeResult decode_unsigned(T &u_num, byte_string_view const enc)
{
    byte_string_view payload{};
    BOOST_OUTCOME_TRY(
        auto const rest_of_enc, parse_string_metadata(payload, enc));
    BOOST_OUTCOME_TRY(u_num, decode_raw_num<T>(payload));
    return rest_of_enc;
}

constexpr DecodeResult decode_bool(bool &target, byte_string_view const enc)
{
    uint64_t i{0};
    BOOST_OUTCOME_TRY(auto ret, decode_unsigned<uint64_t>(i, enc));
    MONAD_DEBUG_ASSERT(i <= 1);
    target = i;
    return ret;
}

inline DecodeResult decode_bytes32(bytes32_t &bytes, byte_string_view const enc)
{
    return decode_byte_array<32>(bytes.bytes, enc);
}

inline DecodeResult
decode_address(address_t &address, byte_string_view const enc)
{
    return decode_byte_array<20>(address.bytes, enc);
}

inline DecodeResult
decode_address(std::optional<address_t> &address, byte_string_view const enc)
{
    byte_string_view payload{};
    BOOST_OUTCOME_TRY(
        auto const rest_of_enc, parse_string_metadata(payload, enc));
    if (payload.size() == sizeof(address_t)) {
        address = address_t{};
        std::memcpy(address->bytes, payload.data(), sizeof(address_t));
    }
    else {
        MONAD_ASSERT(payload.size() == 0);
        address.reset();
    }
    return rest_of_enc;
}

DecodeResult decode_sc(SignatureAndChain &, byte_string_view);
DecodeResult decode_bloom(Receipt::Bloom &, byte_string_view);
DecodeResult decode_topics(std::vector<bytes32_t> &, byte_string_view);
DecodeResult decode_log(Receipt::Log &, byte_string_view);
DecodeResult decode_logs(std::vector<Receipt::Log> &, byte_string_view);

DecodeResult
decode_access_entry_keys(std::vector<bytes32_t> &, byte_string_view);
DecodeResult decode_access_entry(Transaction::AccessEntry &, byte_string_view);
DecodeResult decode_access_list(Transaction::AccessList &, byte_string_view);

DecodeResult
decode_account(Account &, bytes32_t &storage_root, byte_string_view);
DecodeResult decode_transaction(Transaction &, byte_string_view);
DecodeResult decode_receipt(Receipt &, byte_string_view);
DecodeResult decode_withdrawal(Withdrawal &, byte_string_view);
DecodeResult
decode_withdrawal_list(std::vector<Withdrawal> &, byte_string_view);

DecodeResult decode_block(Block &, byte_string_view);
DecodeResult get_rlp_header_from_block(byte_string_view);

MONAD_RLP_NAMESPACE_END
