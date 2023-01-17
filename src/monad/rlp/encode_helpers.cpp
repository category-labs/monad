#include <monad/rlp/encode_helpers.hpp>

#include <monad/core/account.hpp>
#include <monad/core/assert.h>
#include <monad/core/signature.hpp>
#include <monad/core/transaction.hpp>

MONAD_RLP_NAMESPACE_BEGIN

byte_string encode_account(Account const &account, bytes32_t const &code_root)
{
    return encode_list(
        encode_unsigned(account.nonce),
        encode_unsigned(account.balance),
        encode_bytes32(code_root),
        encode_bytes32(account.code_hash));
}

byte_string encode(Transaction const &txn)
{
    MONAD_ASSERT(txn.to != std::nullopt);
    const auto v = get_v(txn.sc);

    if (txn.type == Transaction::Type::eip155) {
        return encode_list(
            encode_unsigned(txn.nonce),
            encode_unsigned(txn.gas_price),
            encode_unsigned(txn.gas_limit),
            encode_address(*(txn.to)),
            encode_unsigned(txn.amount),
            encode_string(txn.data),
            encode_unsigned(v),
            encode_unsigned(txn.sc.r),
            encode_unsigned(txn.sc.s));
    }
    return encode_list();
}

MONAD_RLP_NAMESPACE_END
