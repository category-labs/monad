#include <monad/rlp/decode_helpers.hpp>

#include <monad/core/account.hpp>
#include <monad/core/address.hpp>
#include <monad/core/assert.h>

MONAD_RLP_NAMESPACE_BEGIN

byte_string_view
decode_account(Account &acc, bytes32_t &code_root, byte_string_view const enc)
{
    byte_string_view payload{};
    auto const rest_of_enc = parse_list_metadata(payload, enc);

    payload = decode_unsigned<uint64_t>(acc.nonce, payload);
    payload = decode_unsigned<uint256_t>(acc.balance, payload);
    payload = decode_bytes32(code_root, payload);
    payload = decode_bytes32(acc.code_hash, payload);

    MONAD_ASSERT(payload.size() == 0);
    return rest_of_enc;
}

MONAD_RLP_NAMESPACE_END