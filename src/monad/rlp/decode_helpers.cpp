#include <monad/rlp/decode_helpers.hpp>

#include <monad/core/account.hpp>
#include <monad/core/address.hpp>
#include <monad/core/assert.h>

MONAD_RLP_NAMESPACE_BEGIN

byte_string_view decode_sc(SignatureAndChain &sc, byte_string_view const enc)
{
    uint64_t v{};
    const auto rest_of_enc = decode_unsigned<uint64_t>(v, enc);

    sc.from_v(v);
    return rest_of_enc;
}

byte_string_view decode_access_entry_keys(
    std::vector<bytes32_t> &keys, byte_string_view const enc)
{
    byte_string_view payload{};
    const auto rest_of_enc = parse_list_metadata(payload, enc);
    const byte_string_loc key_size =
        33; // 1 byte for header, 32 bytes for byte32_t
    const byte_string_loc list_space = payload.size();
    MONAD_ASSERT(keys.size() == 0);
    keys.reserve(list_space / key_size);

    while (payload.size() > 0) {
        bytes32_t key{};
        payload = decode_bytes32(key, payload);
        keys.emplace_back(key);
    }

    MONAD_ASSERT(list_space == keys.size() * key_size);
    return rest_of_enc;
}

byte_string_view
decode_access_entry(Transaction::AccessEntry &ae, byte_string_view const enc)
{
    byte_string_view payload{};
    const auto rest_of_enc = parse_list_metadata(payload, enc);

    payload = decode_address(ae.a, payload);
    payload = decode_access_entry_keys(ae.keys, payload);

    MONAD_ASSERT(payload.size() == 0);
    return rest_of_enc;
}

byte_string_view
decode_access_list(Transaction::AccessList &al, byte_string_view const enc)
{
    byte_string_view payload{};
    const auto rest_of_enc = parse_list_metadata(payload, enc);
    const byte_string_loc approx_num_keys = 10;
    // 20 bytes for address, 33 bytes per key
    const byte_string_loc access_entry_size_approx = 20 + 33 * approx_num_keys;
    const byte_string_loc list_space = payload.size();
    al.reserve(list_space / access_entry_size_approx);

    while (payload.size() > 0) {
        Transaction::AccessEntry ae{};
        payload = decode_access_entry(ae, payload);
        al.emplace_back(ae);
    }

    MONAD_ASSERT(payload.size() == 0);
    return rest_of_enc;
}

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

byte_string_view
decode_transaction(Transaction &txn, byte_string_view const enc)
{
    MONAD_ASSERT(enc.size() > 0);

    // Transaction type matching
    byte_string_loc i = 0;
    const uint8_t &type = enc[i];
    if (type == 0x01) // eip2930
    {
        ++i;
        txn.type = Transaction::Type::eip2930;
    }
    else if (type == 0x02) // eip1559
    {
        ++i;
        txn.type = Transaction::Type::eip1559;
    }
    else // eip155
    {
        txn.type = Transaction::Type::eip155;
    }

    byte_string_view payload{};
    const auto rest_of_enc =
        parse_list_metadata(payload, enc.substr(i, enc.size() - i));
    if (txn.type == Transaction::Type::eip155) {
        payload = decode_unsigned<uint64_t>(txn.nonce, payload);
        payload = decode_unsigned<uint64_t>(txn.gas_price, payload);
        payload = decode_unsigned<uint64_t>(txn.gas_limit, payload);
        payload = decode_address(*txn.to, payload);

        payload = decode_unsigned<uint128_t>(txn.amount, payload);
        payload = decode_string(txn.data, payload);
        payload = decode_sc(txn.sc, payload);
        payload = decode_unsigned<uint256_t>(txn.sc.r, payload);
        payload = decode_unsigned<uint256_t>(txn.sc.s, payload);
    }
    else if (txn.type == Transaction::Type::eip1559) {
        payload = decode_unsigned<uint64_t>(*txn.sc.chain_id, payload);
        payload = decode_unsigned<uint64_t>(txn.nonce, payload);
        payload = decode_unsigned<uint64_t>(txn.priority_fee, payload);
        payload = decode_unsigned<uint64_t>(txn.gas_price, payload);
        payload = decode_unsigned<uint64_t>(txn.gas_limit, payload);
        payload = decode_address(*txn.to, payload);
        payload = decode_unsigned<uint128_t>(txn.amount, payload);
        payload = decode_string(txn.data, payload);
        payload = decode_access_list(txn.access_list, payload);
        payload = decode_bool(txn.sc.odd_y_parity, payload);
        payload = decode_unsigned<uint256_t>(txn.sc.r, payload);
        payload = decode_unsigned<uint256_t>(txn.sc.s, payload);
    }
    else // Transaction::type::eip2930
    {
        payload = decode_unsigned<uint64_t>(*txn.sc.chain_id, payload);
        payload = decode_unsigned<uint64_t>(txn.nonce, payload);
        payload = decode_unsigned<uint64_t>(txn.gas_price, payload);
        payload = decode_unsigned<uint64_t>(txn.gas_limit, payload);
        payload = decode_address(*txn.to, payload);
        payload = decode_unsigned<uint128_t>(txn.amount, payload);
        payload = decode_string(txn.data, payload);
        payload = decode_access_list(txn.access_list, payload);
        payload = decode_bool(txn.sc.odd_y_parity, payload);
        payload = decode_unsigned<uint256_t>(txn.sc.r, payload);
        payload = decode_unsigned<uint256_t>(txn.sc.s, payload);
    }
    txn.from = std::nullopt;

    MONAD_ASSERT(payload.size() == 0);
    return rest_of_enc;
}

MONAD_RLP_NAMESPACE_END
