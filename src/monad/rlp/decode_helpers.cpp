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

inline bytes32_t decode_bytes32(byte_string_view const enc, byte_string_loc &i) {
    auto dec = decode_string(enc, i);
    MONAD_ASSERT(dec.size() == 32);

    bytes32_t res;
    // glee for shea: is memcpy appropriate?
    memcpy(res.bytes, dec.data(), 32);

    return res;
}

inline address_t decode_address(byte_string_view const enc, byte_string_loc &i) {
    auto dec = decode_string(enc, i);
    MONAD_ASSERT(dec.size() == 20);

    address_t res;
    // glee for shea: is memcpy appropriate?
    memcpy(res.bytes, dec.data(), 20);

    return res;
}

inline SignatureAndChain decode_sc(byte_string_view const enc, byte_string_loc &i) {
    auto dec = decode_unsigned(enc, i);

    SignatureAndChain res;
    from_v(res, dec);

    return res;
}

// glee for glee: TODO vector.resize() based on rlp-length to avoid unnecessary
//                resizing on push_back()

std::vector<bytes32_t> decode_access_entry_keys(byte_string_view const enc, byte_string_loc &i)
{
    MONAD_ASSERT(i < enc.size());
    std::vector<bytes32_t> keys;

    byte_string_loc length;
    const uint8_t &first = enc[i];
    ++i;
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
    const byte_string_loc end = i + length;
    MONAD_ASSERT(end <= enc.size());

    while (i < end)
    {
        bytes32_t key = decode_bytes32(enc, i);
        keys.emplace_back(key);
    }

    MONAD_ASSERT(i == end);
    return keys;
}

Transaction::AccessEntry decode_access_entry(byte_string_view const enc, byte_string_loc &i)
{
    MONAD_ASSERT(i < enc.size());
    Transaction::AccessEntry ae;

    byte_string_loc length;
    const uint8_t &first = enc[i];
    ++i;
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
    const byte_string_loc end = i + length;
    MONAD_ASSERT(end <= enc.size());

    while (i < end)
    {
        ae.a = decode_address(enc, i);
        ae.keys = decode_access_entry_keys(enc, i);
    }

    MONAD_ASSERT(i == end);
    return ae;
}

Transaction::AccessList decode_access_list(byte_string_view const enc, byte_string_loc &i)
{
    MONAD_ASSERT(i < enc.size());
    Transaction::AccessList al;

    byte_string_loc length;
    const uint8_t &first = enc[i];
    ++i;
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
    const byte_string_loc end = i + length;
    MONAD_ASSERT(end <= enc.size());

    while (i < end)
    {
        al.emplace_back(decode_access_entry(enc, i));
    }

    MONAD_ASSERT(i == end);
    return al;
}

std::pair<Account, bytes32_t> decode_account(byte_string_view const enc, byte_string_loc &i)
{
    MONAD_ASSERT(i < enc.size());
    Account acc;
    bytes32_t code_root;

    const uint8_t &first = enc[i];
    ++i;
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
    const byte_string_loc end = i + length;
    MONAD_ASSERT(end <= enc.size());

    acc.nonce = decode_unsigned(enc, i);
    acc.balance = decode_unsigned(enc, i);
    code_root = decode_bytes32(enc, i);
    acc.code_hash = decode_bytes32(enc, i);

    MONAD_ASSERT(i == end);
    return std::make_pair(acc, code_root);
}

Transaction decode_transaction(byte_string_view const enc, byte_string_loc &i)
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

    MONAD_ASSERT(i < enc.size());
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
    const byte_string_loc end = i + length;
    MONAD_ASSERT(end <= enc.size());

    if (txn.type == Transaction::Type::eip155)
    {
        txn.nonce = decode_unsigned(enc, i);
        txn.gas_price = decode_unsigned(enc, i);
        txn.gas_limit = decode_unsigned(enc, i);
        *txn.to = decode_address(enc, i);
        txn.amount = decode_unsigned(enc, i);
        txn.data = decode_string(enc, i);
        txn.sc = decode_sc(enc, i);
        txn.sc.r = decode_unsigned(enc, i);
        txn.sc.s = decode_unsigned(enc, i);
    }
    else if (txn.type == Transaction::Type::eip1559)
    {
        *txn.sc.chain_id = decode_unsigned(enc, i);
        txn.nonce = decode_unsigned(enc, i);
        txn.priority_fee = decode_unsigned(enc, i);
        txn.gas_price = decode_unsigned(enc, i);
        txn.gas_limit = decode_unsigned(enc, i);
        *txn.to = decode_address(enc, i);
        txn.amount = decode_unsigned(enc, i);
        txn.data = decode_string(enc, i);
        txn.access_list = decode_access_list(enc, i);
        txn.sc.odd_y_parity = decode_unsigned(enc, i);
        txn.sc.r = decode_unsigned(enc, i);
        txn.sc.s = decode_unsigned(enc, i);
    }
    else            // Transaction::type::eip2930
    {
        *txn.sc.chain_id = decode_unsigned(enc, i);
        txn.nonce = decode_unsigned(enc, i);
        txn.gas_price = decode_unsigned(enc, i);
        txn.gas_limit = decode_unsigned(enc, i);
        *txn.to = decode_address(enc, i);
        txn.amount = decode_unsigned(enc, i);
        txn.data = decode_string(enc, i);
        txn.access_list = decode_access_list(enc, i);
        txn.sc.odd_y_parity = decode_unsigned(enc, i);
        txn.sc.r = decode_unsigned(enc, i);
        txn.sc.s = decode_unsigned(enc, i);
    }

    MONAD_ASSERT(i == end);
    return txn;
}

MONAD_RLP_NAMESPACE_END