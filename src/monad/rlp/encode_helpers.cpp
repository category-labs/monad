#include <monad/rlp/encode_helpers.hpp>

#include <monad/core/account.hpp>
#include <monad/core/assert.h>
#include <monad/core/receipt.hpp>
#include <monad/core/signature.hpp>
#include <monad/core/transaction.hpp>

#include <monad/trie/compact_encode.hpp>
#include <monad/trie/node.hpp>

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

byte_string
encode_account(Account const &account, bytes32_t const &storage_root)
{
    return encode_list(
        encode_unsigned(account.nonce),
        encode_unsigned(account.balance),
        encode_bytes32(storage_root),
        encode_bytes32(account.code_hash));
}

byte_string encode_transaction(Transaction const &txn)
{
    if (txn.type == Transaction::Type::eip155) {
        return encode_list(
            encode_unsigned(txn.nonce),
            encode_unsigned(txn.gas_price),
            encode_unsigned(txn.gas_limit),
            encode_address(txn.to),
            encode_unsigned(txn.amount),
            encode_string(txn.data),
            encode_unsigned(get_v(txn.sc)),
            encode_unsigned(txn.sc.r),
            encode_unsigned(txn.sc.s));
    }

    MONAD_ASSERT(txn.sc.chain_id != std::nullopt);

    if (txn.type == Transaction::Type::eip1559) {
        return encode_string(
            byte_string{0x02} += encode_list(
                encode_unsigned(txn.sc.chain_id.value_or(0)),
                encode_unsigned(txn.nonce),
                encode_unsigned(txn.priority_fee),
                encode_unsigned(txn.gas_price),
                encode_unsigned(txn.gas_limit),
                encode_address(txn.to),
                encode_unsigned(txn.amount),
                encode_string(txn.data),
                encode_access_list(txn.access_list),
                encode_unsigned(static_cast<unsigned>(txn.sc.odd_y_parity)),
                encode_unsigned(txn.sc.r),
                encode_unsigned(txn.sc.s)));
    }
    else if (txn.type == Transaction::Type::eip2930) {
        return encode_string(
            byte_string{0x01} += encode_list(
                encode_unsigned(txn.sc.chain_id.value_or(0)),
                encode_unsigned(txn.nonce),
                encode_unsigned(txn.gas_price),
                encode_unsigned(txn.gas_limit),
                encode_address(txn.to),
                encode_unsigned(txn.amount),
                encode_string(txn.data),
                encode_access_list(txn.access_list),
                encode_unsigned(static_cast<unsigned>(txn.sc.odd_y_parity)),
                encode_unsigned(txn.sc.r),
                encode_unsigned(txn.sc.s)));
    }
    assert(false);
    return {};
}

byte_string encode_transaction_for_signing(Transaction const &txn)
{
    if (txn.type == Transaction::Type::eip155) {
        if (txn.sc.chain_id.has_value()) {
            return encode_list(
                encode_unsigned(txn.nonce),
                encode_unsigned(txn.gas_price),
                encode_unsigned(txn.gas_limit),
                encode_address(txn.to),
                encode_unsigned(txn.amount),
                encode_string(txn.data),
                encode_unsigned(txn.sc.chain_id.value_or(0)),
                encode_unsigned(0u),
                encode_unsigned(0u));
        }
        else {
            return encode_list(
                encode_unsigned(txn.nonce),
                encode_unsigned(txn.gas_price),
                encode_unsigned(txn.gas_limit),
                encode_address(txn.to),
                encode_unsigned(txn.amount),
                encode_string(txn.data));
        }
    }

    MONAD_ASSERT(txn.sc.chain_id != std::nullopt);

    if (txn.type == Transaction::Type::eip1559) {
        return byte_string{0x02} +
               encode_list(
                   encode_unsigned(txn.sc.chain_id.value_or(0)),
                   encode_unsigned(txn.nonce),
                   encode_unsigned(txn.priority_fee),
                   encode_unsigned(txn.gas_price),
                   encode_unsigned(txn.gas_limit),
                   encode_address(txn.to),
                   encode_unsigned(txn.amount),
                   encode_string(txn.data),
                   encode_access_list(txn.access_list));
    }
    else if (txn.type == Transaction::Type::eip2930) {
        return byte_string{0x01} +
               encode_list(
                   encode_unsigned(txn.sc.chain_id.value_or(0)),
                   encode_unsigned(txn.nonce),
                   encode_unsigned(txn.gas_price),
                   encode_unsigned(txn.gas_limit),
                   encode_address(txn.to),
                   encode_unsigned(txn.amount),
                   encode_string(txn.data),
                   encode_access_list(txn.access_list));
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

    for (auto const &i : r.logs) {
        log_result += encode_log(i);
    }

    auto const receipt_bytes = encode_list(
        encode_unsigned(r.status),
        encode_unsigned(r.gas_used),
        encode_bloom(r.bloom),
        encode_list(log_result));

    if (r.type == Transaction::Type::eip1559 ||
        r.type == Transaction::Type::eip2930) {
        return encode_string(
            static_cast<unsigned char>(r.type) + receipt_bytes);
    }
    return receipt_bytes;
}

byte_string encode_withdrawal(Withdrawal const &withdrawal)
{
    return encode_list(
        encode_unsigned(withdrawal.index),
        encode_unsigned(withdrawal.validator_index),
        encode_address(withdrawal.recipient),
        encode_unsigned(withdrawal.amount));
}

byte_string encode_leaf(trie::Leaf const &leaf)
{
    return encode_list(
        encode_string(trie::compact_encode(leaf.partial_path(), true)),
        encode_string(leaf.value));
}

byte_string encode_branch(trie::Branch const &branch)
{
    auto const branch_rlp = encode_list(
        branch.children[0],
        branch.children[1],
        branch.children[2],
        branch.children[3],
        branch.children[4],
        branch.children[5],
        branch.children[6],
        branch.children[7],
        branch.children[8],
        branch.children[9],
        branch.children[10],
        branch.children[11],
        branch.children[12],
        branch.children[13],
        branch.children[14],
        branch.children[15],
        encode_string(byte_string{}));

    auto const partial_path = branch.partial_path();
    if (partial_path.empty()) {
        return branch_rlp;
    }

    return encode_list(
        encode_string(trie::compact_encode(partial_path, false)),
        to_node_reference(branch_rlp));
}

byte_string to_node_reference(byte_string_view rlp)
{
    if (rlp.size() < 32) {
        return byte_string(rlp);
    }

    auto const hash = ethash::keccak256(rlp.data(), rlp.size());
    return encode_string(to_byte_string_view(hash.bytes));
}

MONAD_RLP_NAMESPACE_END
