#include <monad/rlp/decode_helpers.hpp>

#include <monad/core/account.hpp>
#include <monad/core/assert.h>
#include <monad/core/receipt.hpp>
#include <monad/core/signature.hpp>
#include <monad/core/transaction.hpp>

#include <numeric>
#include <string>

MONAD_RLP_NAMESPACE_BEGIN

std::pair<Account, bytes32_t> decode_account(byte_string_view const enc) {
    MONAD_ASSERT(enc.size() > 0);
    Account acc;
    bytes32_t code_root;

    const uint8_t &first = enc[0];
    byte_string_loc i = 1;
    uint8_t length;
    MONAD_ASSERT(first >= 192);
    if (first < 248)        // [192, 247]
    {
        length = first - 192;
        MONAD_ASSERT(i + length == enc.size());

        {
            auto dec = decode_unsigned(enc, i);
            acc.nonce = dec.first;
            i = dec.second;
        }

        {
            auto dec = decode_unsigned(enc, i);
            acc.balance = dec.first;
            i = dec.second;
        }

        // glee for shea: is memcpy appropriate?
        {
            auto dec = decode_string(enc, i);
            MONAD_ASSERT(dec.first.size() == 32);
            memcpy(code_root.bytes, dec.first.data(), 32);
            i = dec.second;
        }

        {
            auto dec = decode_string(enc, i);
            MONAD_ASSERT(dec.first.size() == 32);
            memcpy(acc.code_hash.bytes, dec.first.data(), 32);
            i = dec.second;
        }

        MONAD_ASSERT(i == enc.size());
    }
    else                    // [248, 255]
    {
        // TODO
        MONAD_ASSERT(false);
    }
    return std::make_pair(acc, code_root);
}

MONAD_RLP_NAMESPACE_END
