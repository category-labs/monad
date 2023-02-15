#include <monad/rlp/encode_helpers.hpp>

#include <monad/core/account.hpp>
#include <monad/core/assert.h>
#include <monad/core/receipt.hpp>
#include <monad/core/signature.hpp>
#include <monad/core/transaction.hpp>

#include <numeric>
#include <string>

MONAD_RLP_NAMESPACE_BEGIN

byte_string encode_access_list(Transaction::AccessList const &list)
{
    byte_string result{};
    for (auto const &i : list) {
        result += encode_list(
            encode_address(i.a) + encode_list(std::accumulate(
                                      std::cbegin(i.keys),
                                      std::cend(i.keys),
                                      result,
                                      [](auto const i, auto const j) {
                                          return std::move(i) +
                                                 encode_bytes32(j);
                                      })));
    };

    return encode_list(result);
}

byte_string encode_account(Account const &account, bytes32_t const &code_root)
{
    return encode_list(
        encode_unsigned(account.nonce),
        encode_unsigned(account.balance),
        encode_bytes32(code_root),
        encode_bytes32(account.code_hash));
}

byte_string encode_transaction(Transaction const &txn)
{
    MONAD_ASSERT(txn.to != std::nullopt);

    if (txn.type == Transaction::Type::eip155) {
        return encode_list(
            encode_unsigned(txn.nonce),
            encode_unsigned(txn.gas_price),
            encode_unsigned(txn.gas_limit),
            encode_address(*(txn.to)),
            encode_unsigned(txn.amount),
            encode_string(txn.data),
            encode_unsigned(get_v(txn.sc)),
            encode_unsigned(txn.sc.r),
            encode_unsigned(txn.sc.s));
    }

    MONAD_ASSERT(txn.sc.chain_id != std::nullopt);

    if (txn.type == Transaction::Type::eip1559) {
        return byte_string{0x02} += encode_list(
                   encode_unsigned(*txn.sc.chain_id),
                   encode_unsigned(txn.nonce),
                   encode_unsigned(txn.priority_fee),
                   encode_unsigned(txn.gas_price),
                   encode_unsigned(txn.gas_limit),
                   encode_address(*(txn.to)),
                   encode_unsigned(txn.amount),
                   encode_string(txn.data),
                   encode_access_list(txn.access_list),
                   encode_unsigned(static_cast<unsigned>(txn.sc.odd_y_parity)),
                   encode_unsigned(txn.sc.r),
                   encode_unsigned(txn.sc.s));
    }
    else if (txn.type == Transaction::Type::eip2930) {
        return byte_string{0x01} += encode_list(
                   encode_unsigned(*txn.sc.chain_id),
                   encode_unsigned(txn.nonce),
                   encode_unsigned(txn.gas_price),
                   encode_unsigned(txn.gas_limit),
                   encode_address(*(txn.to)),
                   encode_unsigned(txn.amount),
                   encode_string(txn.data),
                   encode_access_list(txn.access_list),
                   encode_unsigned(static_cast<unsigned>(txn.sc.odd_y_parity)),
                   encode_unsigned(txn.sc.r),
                   encode_unsigned(txn.sc.s));
    }
    assert(false);
    return {};
}

byte_string encode_topics(std::vector<bytes32_t> const &t)
{
    byte_string result{};
    for (auto const &i : t) {
        result += encode_bytes32(i);
    }
    return encode_list(result);
}

byte_string encode_log(Receipt::Log const &l)
{
    return encode_list(
        encode_address(l.address),
        encode_topics(l.topics),
        encode_list(l.data));
}

byte_string encode_bloom(Receipt::Bloom const &b)
{
    return encode_string(to_byte_string_view(b));
}

byte_string encode_receipt(Receipt const &r)
{
    byte_string log_result{};
    byte_string prefix{};

    for (auto const &i : r.logs) {
        log_result += encode_log(i);
    }

    if (r.type == Transaction::Type::eip1559 ||
        r.type == Transaction::Type::eip2930) {
        prefix = static_cast<unsigned>(r.type);
    }

    return prefix + encode_list(
                        encode_unsigned(r.status),
                        encode_unsigned(r.gas_used),
                        encode_bloom(r.bloom),
                        encode_list(log_result));
}

MONAD_RLP_NAMESPACE_END