#pragma once

#include <monad/rlp/config.hpp>
#include <monad/rlp/decode.hpp>
#include <monad/rlp/util.hpp>

#include <monad/core/account.hpp>
#include <monad/core/address.hpp>
#include <monad/core/block.hpp>
#include <monad/core/byte_string.hpp>
#include <monad/core/receipt.hpp>
#include <monad/core/signature.hpp>
#include <monad/core/transaction.hpp>

MONAD_RLP_NAMESPACE_BEGIN

template <unsigned_integral T>
inline constexpr byte_string_view
decode_unsigned(T &u_num, byte_string_view const enc)
{
    byte_string_view payload{};
    auto const rest_of_enc = parse_string_metadata(payload, enc);
    u_num = decode_raw_num<T>(payload);
    return rest_of_enc;
}

inline byte_string_view
decode_bytes32(bytes32_t &bytes, byte_string_view const enc)
{
    return decode_byte_array<32>(bytes.bytes, enc);
}

inline byte_string_view
decode_address(address_t &address, byte_string_view const enc)
{
    return decode_byte_array<20>(address.bytes, enc);
}

inline byte_string_view
decode_address_optional(std::optional<address_t> &address, byte_string_view const enc)
{
    byte_string_view payload{};
    auto const rest_of_enc = parse_string_metadata(payload, enc);
    if (payload.size() == sizeof(address_t)) {
        std::memcpy(address->bytes, payload.data(), sizeof(address_t));
    } else {
        MONAD_ASSERT(payload.size() == 0);
        address.reset();
    }
    return rest_of_enc;
}

byte_string_view decode_sc(SignatureAndChain &sc, byte_string_view const enc);
byte_string_view
decode_bloom(Receipt::Bloom &bloom, byte_string_view const enc);
byte_string_view decode_log_data(byte_string &data, byte_string_view enc);
byte_string_view
decode_topics(std::vector<bytes32_t> &topics, byte_string_view enc);
byte_string_view decode_log(Receipt::Log &log, byte_string_view enc);
byte_string_view
decode_logs(std::vector<Receipt::Log> &logs, byte_string_view const enc);

byte_string_view decode_access_entry_keys(
    std::vector<bytes32_t> &keys, byte_string_view const enc);
byte_string_view
decode_access_entry(Transaction::AccessEntry &ae, byte_string_view const enc);
byte_string_view
decode_access_list(Transaction::AccessList &al, byte_string_view const enc);

byte_string_view
decode_account(Account &acc, bytes32_t &code_root, byte_string_view const enc);
byte_string_view
decode_transaction(Transaction &txn, byte_string_view const enc);
byte_string_view decode_receipt(Receipt &receipt, byte_string_view const enc);
byte_string_view decode_block(Block &block, byte_string_view const enc);

MONAD_RLP_NAMESPACE_END
