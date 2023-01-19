#include <monad/rlp/encode_helpers.hpp>

#include <monad/core/account.hpp>

MONAD_RLP_NAMESPACE_BEGIN

byte_string encode_account(Account const &account, bytes32_t const &code_root)
{
    return encode_list(
        encode_unsigned(account.nonce),
        encode_unsigned(account.balance),
        encode_bytes32(code_root),
        encode_bytes32(account.code_hash));
}

MONAD_RLP_NAMESPACE_END
