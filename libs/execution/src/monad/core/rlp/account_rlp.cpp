#include <monad/core/account.hpp>
#include <monad/core/byte_string.hpp>
#include <monad/core/bytes.hpp>
#include <monad/core/int.hpp>
#include <monad/core/likely.h>
#include <monad/core/result.hpp>
#include <monad/core/rlp/account_rlp.hpp>
#include <monad/core/rlp/bytes_rlp.hpp>
#include <monad/core/rlp/int_rlp.hpp>
#include <monad/rlp/config.hpp>
#include <monad/rlp/decode.hpp>
#include <monad/rlp/decode_error.hpp>
#include <monad/rlp/encode2.hpp>

#include <boost/outcome/try.hpp>

#include <cstdint>

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

Result<Account> decode_account(bytes32_t &storage_root, byte_string_view &enc)
{
    BOOST_OUTCOME_TRY(auto payload, parse_list_metadata(enc));

    Account acct;
    BOOST_OUTCOME_TRY(acct.nonce, decode_unsigned<uint64_t>(payload));
    BOOST_OUTCOME_TRY(acct.balance, decode_unsigned<uint256_t>(payload));
    BOOST_OUTCOME_TRY(storage_root, decode_bytes32(payload));
    BOOST_OUTCOME_TRY(acct.code_hash, decode_bytes32(payload));

    if (MONAD_UNLIKELY(!payload.empty())) {
        return DecodeError::InputTooLong;
    }

    return acct;
}

MONAD_RLP_NAMESPACE_END
