#include <monad/rlp/decode_helpers.hpp>

#include <monad/core/account.hpp>
#include <monad/core/address.hpp>
#include <monad/core/assert.h>
#include <monad/core/receipt.hpp>
#include <monad/core/signature.hpp>
#include <monad/core/transaction.hpp>

#include <numeric>
#include <string>

MONAD_RLP_NAMESPACE_BEGIN

template <typename T>
inline void decode_unsigned_to_field_and_update_ptr(byte_string_view const enc, T &field, byte_string_loc &i) {
    auto dec_with_ptr = decode_unsigned(enc, i);
    field = dec_with_ptr.decoding;
    i = dec_with_ptr.ptr;
}

inline void decode_string_to_field_and_update_ptr(byte_string_view const enc, byte_string &field, byte_string_loc &i) {
    auto dec_with_ptr = decode_string(enc, i);
    field = dec_with_ptr.decoding;
    i = dec_with_ptr.ptr;
}

inline void decode_bytes32_to_field_and_update_ptr(byte_string_view const enc, bytes32_t &field, byte_string_loc &i) {
    auto dec_with_ptr = decode_string(enc, i);
    MONAD_ASSERT(dec_with_ptr.decoding.size() == 32);
    // glee for shea: is memcpy appropriate?
    memcpy(field.bytes, dec_with_ptr.decoding.data(), 32);
    i = dec_with_ptr.ptr;
}

inline void decode_address_to_field_and_update_ptr(byte_string_view const enc, address_t &field, byte_string_loc &i) {
    auto dec_with_ptr = decode_string(enc, i);
    MONAD_ASSERT(dec_with_ptr.decoding.size() == 20);
    // glee for shea: is memcpy appropriate?
    memcpy(field.bytes, dec_with_ptr.decoding.data(), 20);
    i = dec_with_ptr.ptr;
}

inline void decode_sc_to_field_and_update_ptr(byte_string_view const enc, SignatureAndChain &sc, byte_string_loc &i) {
    auto dec_with_ptr = decode_unsigned(enc, i);
    from_v(sc, dec_with_ptr.decoding);
    i = dec_with_ptr.ptr;
}

std::pair<Account, bytes32_t> decode_account(byte_string_view const enc)
{
    MONAD_ASSERT(enc.size() > 0);
    Account acc;
    bytes32_t code_root;

    const uint8_t &first = enc[0];
    byte_string_loc i = 1;
    byte_string_loc length;
    MONAD_ASSERT(first >= 192);
    /**
     * glee (& tong) for shea: this branch will never really occur because of
     * the `bytes32_t` fields... should we consider MONAD_ASSERT(first >= 248)?
     */
    if (first < 248)
    {
        length = first - 192;
    }
    else
    {
        byte_string_loc length_of_length;
        length_of_length = first - 247;
        MONAD_ASSERT(i + length_of_length < enc.size());

        length = decode_length(enc, i, length_of_length);
        i += length_of_length;
    }
    MONAD_ASSERT(i + length == enc.size());

    decode_unsigned_to_field_and_update_ptr(enc, acc.nonce, i);
    decode_unsigned_to_field_and_update_ptr(enc, acc.balance, i);
    decode_bytes32_to_field_and_update_ptr(enc, code_root, i);
    decode_bytes32_to_field_and_update_ptr(enc, acc.code_hash, i);

    MONAD_ASSERT(i == enc.size());
    return std::make_pair(acc, code_root);
}

decoding_with_updated_ptr<Transaction> decode_transaction(byte_string_view const enc, byte_string_loc i)
{
    MONAD_ASSERT(i < enc.size());
    Transaction txn;

    const uint8_t &type = enc[i];

    // Transaction type matching
    if (type == 0x01)      // eip2930
    {
        ++i;
        txn.type = Transaction::Type::eip2930;
    }
    else if (type == 0x02) // eip1559
    {
        ++i;
        txn.type = Transaction::Type::eip1559;
    }
    else                    // eip155
    {
        txn.type = Transaction::Type::eip155;
    }

    const uint8_t &first = enc[i];

    ++i;
    byte_string_loc length;
    MONAD_ASSERT(first >= 192);
    if (first < 248)
    {
        length = first - 192;
    }
    else
    {
        byte_string_loc length_of_length;
        length_of_length = first - 247;
        MONAD_ASSERT(i + length_of_length < enc.size());

        length = decode_length(enc, i, length_of_length);
        i += length_of_length;
    }
    MONAD_ASSERT(i + length == enc.size());

    if (txn.type == Transaction::Type::eip155)
    {
        decode_unsigned_to_field_and_update_ptr(enc, txn.nonce, i);
        decode_unsigned_to_field_and_update_ptr(enc, txn.gas_price, i);
        decode_unsigned_to_field_and_update_ptr(enc, txn.gas_limit, i);
        decode_address_to_field_and_update_ptr(enc, *txn.to, i);
        decode_unsigned_to_field_and_update_ptr(enc, txn.amount, i);
        decode_string_to_field_and_update_ptr(enc, txn.data, i);
        decode_sc_to_field_and_update_ptr(enc, txn.sc, i);
        decode_unsigned_to_field_and_update_ptr(enc, txn.sc.r, i);
        decode_unsigned_to_field_and_update_ptr(enc, txn.sc.s, i);
    }
    else if (txn.type == Transaction::Type::eip1559)
    {
        decode_unsigned_to_field_and_update_ptr(enc, *txn.sc.chain_id, i);
        decode_unsigned_to_field_and_update_ptr(enc, txn.nonce, i);
        decode_unsigned_to_field_and_update_ptr(enc, txn.priority_fee, i);
        decode_unsigned_to_field_and_update_ptr(enc, txn.gas_price, i);
        decode_unsigned_to_field_and_update_ptr(enc, txn.gas_limit, i);
        decode_address_to_field_and_update_ptr(enc, *txn.to, i);
        decode_unsigned_to_field_and_update_ptr(enc, txn.amount, i);
        decode_string_to_field_and_update_ptr(enc, txn.data, i);
        // TODO access list
        decode_unsigned_to_field_and_update_ptr(enc, txn.sc.odd_y_parity, i);
        decode_unsigned_to_field_and_update_ptr(enc, txn.sc.r, i);
        decode_unsigned_to_field_and_update_ptr(enc, txn.sc.s, i);
    }
    else            // Transaction::type::eip2930
    {
        decode_unsigned_to_field_and_update_ptr(enc, *txn.sc.chain_id, i);
        decode_unsigned_to_field_and_update_ptr(enc, txn.nonce, i);
        decode_unsigned_to_field_and_update_ptr(enc, txn.gas_price, i);
        decode_unsigned_to_field_and_update_ptr(enc, txn.gas_limit, i);
        decode_address_to_field_and_update_ptr(enc, *txn.to, i);
        decode_unsigned_to_field_and_update_ptr(enc, txn.amount, i);
        decode_string_to_field_and_update_ptr(enc, txn.data, i);
        // TODO access list
        decode_unsigned_to_field_and_update_ptr(enc, txn.sc.odd_y_parity, i);
        decode_unsigned_to_field_and_update_ptr(enc, txn.sc.r, i);
        decode_unsigned_to_field_and_update_ptr(enc, txn.sc.s, i);
    }

    return {txn, i};
}

MONAD_RLP_NAMESPACE_END