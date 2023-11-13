#include <monad/core/account_rlp.hpp>
#include <monad/core/bytes_rlp.hpp>
#include <monad/core/int_rlp.hpp>
#include <monad/rlp/config.hpp>
#include <monad/rlp/decode.hpp>
#include <monad/rlp/encode2.hpp>

MONAD_RLP_NAMESPACE_BEGIN

byte_string
encode_account(Account const &account, bytes32_t const &storage_root)
{
    return encode_list2(
        encode_unsigned(account.nonce),
        encode_unsigned(account.balance),
        encode_bytes32(storage_root),
        encode_bytes32(account.code_hash));
}

byte_string encode_account(Account const &account)
{
    return encode_list2(
        encode_unsigned(account.nonce),
        encode_unsigned(account.balance),
        encode_bytes32(account.code_hash));
}

byte_string_view decode_account(
    Account &account, bytes32_t &storage_root, byte_string_view const enc)
{
    byte_string_view payload{};
    auto const rest_of_enc = parse_list_metadata(payload, enc);

    payload = decode_unsigned<uint64_t>(account.nonce, payload);
    payload = decode_unsigned<uint256_t>(account.balance, payload);
    payload = decode_bytes32(storage_root, payload);
    payload = decode_bytes32(account.code_hash, payload);

    MONAD_ASSERT(payload.size() == 0);
    return rest_of_enc;
}

byte_string_view decode_account(Account &account, byte_string_view const enc)
{
    byte_string_view payload{};
    auto const rest_of_enc = parse_list_metadata(payload, enc);

    payload = decode_unsigned<uint64_t>(account.nonce, payload);
    payload = decode_unsigned<uint256_t>(account.balance, payload);
    payload = decode_bytes32(account.code_hash, payload);

    MONAD_ASSERT(payload.size() == 0);
    return rest_of_enc;
}

MONAD_RLP_NAMESPACE_END
