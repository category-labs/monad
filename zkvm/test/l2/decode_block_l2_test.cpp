// Copyright (C) 2026 Category Labs, Inc.
//
// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with this program.  If not, see <http://www.gnu.org/licenses/>.

// decode_block_l2 against rlp::decode_block on the same block.
//
// The equality test is the point: decode_block_l2 duplicates one list walk and
// delegates the rest, and nothing in the build keeps the two in step. If a
// field is ever added to rlp::decode_block and not here, this fails rather than
// producing a quietly different block.

#include <category/core/address.hpp>
#include <category/core/assert.h>
#include <category/core/byte_string.hpp>
#include <category/core/test_util/gtest_signal_stacktrace_printer.hpp> // NOLINT
#include <category/execution/ethereum/core/block.hpp>
#include <category/execution/ethereum/core/rlp/block_rlp.hpp>
#include <category/execution/ethereum/core/rlp/transaction_rlp.hpp>
#include <category/execution/ethereum/core/transaction.hpp>
#include <category/execution/ethereum/rlp/encode2.hpp>
#include <zkvm/guest/decode_block_l2.hpp>
#include <zkvm/guest/l2_cipher.hpp>
#include <zkvm/guest/l2_cipher_suite.hpp>
#include <zkvm/guest/l2_ecdh.hpp>

#include <gtest/gtest.h>

#include <array>
#include <cstdint>
#include <optional>
#include <span>
#include <vector>

using namespace monad;

namespace
{
    L2Scalar operator_sk()
    {
        return L2Scalar{{0x0123456789abcdefULL, 2, 3, 4}};
    }

    // Big-endian, the wire order of the witness's seventh field, so that
    // bind_secret is reached the way ffi.cpp reaches it rather than around it.
    std::array<unsigned char, 32> operator_sk_be()
    {
        std::array<unsigned char, 32> be{};
        L2Scalar const sk = operator_sk();
        for (size_t limb = 0; limb < 4; ++limb) {
            for (size_t b = 0; b < 8; ++b) {
                be[8 * (3 - limb) + (7 - b)] =
                    static_cast<unsigned char>(sk.limb[limb] >> (8u * b));
            }
        }
        return be;
    }

    L2Scalar sender_r()
    {
        return L2Scalar{{0xfedcba9876543210ULL, 7, 8, 9}};
    }

    L2CipherContext context()
    {
        L2CipherContext ctx{};
        ctx.version = 1;
        ctx.chain_id = 1;
        ctx.contract = 0x00000000000000000000000000000000cafef00d_address;
        ctx.namespace_id = 42;
        ctx.epoch = 7;
        auto const pk = l2_ecdh(operator_sk(), SECP256K1_G);
        MONAD_ASSERT(pk.has_value());
        l2_point_compress(*pk, std::span<unsigned char, 33>{ctx.operator_pk});
        ctx.constants_digest = l2_constants_digest(ctx);
        return ctx;
    }

    // The decoder takes a secret that has already been bound to its context,
    // so every case below goes through bind_secret rather than handing over a
    // bare scalar -- which is what ffi.cpp does, and the only way the binding
    // gets exercised at all.
    L2Cipher::Secret bound_secret(L2Cipher::Context const &ctx)
    {
        auto const be = operator_sk_be();
        auto const secret =
            L2Cipher::bind_secret(ctx, std::span<unsigned char const, 32>{be});
        MONAD_ASSERT(secret.has_value());
        return *secret;
    }

    Transaction legacy_tx(uint64_t const nonce, byte_string data)
    {
        Transaction tx{};
        tx.sc.signature.r = 1;
        tx.sc.signature.s = 2;
        tx.sc.signature.y_parity = 0;
        tx.nonce = nonce;
        tx.max_fee_per_gas = 7;
        tx.gas_limit = 21'000;
        tx.value = 5;
        tx.to = 0x000000000000000000000000000000000baddcaf_address;
        tx.type = TransactionType::legacy;
        tx.data = std::move(data);
        return tx;
    }

    Block sample_block()
    {
        Block b{};
        b.header.number = 1234;
        b.header.gas_limit = 30'000'000;
        b.header.timestamp = 1'700'000'000;
        b.transactions.push_back(legacy_tx(0, {}));
        b.transactions.push_back(
            legacy_tx(1, byte_string{0xde, 0xad, 0xbe, 0xef}));
        b.transactions.push_back(legacy_tx(2, byte_string(200, 0x5a)));
        return b;
    }

    /// The L2 body: the same header and ommers, but a transactions list whose
    /// every item is an RLP string holding one ciphertext.
    byte_string encode_l2_block(
        BlockHeader const &header, std::vector<byte_string> const &ciphertexts)
    {
        byte_string txs;
        for (auto const &ct : ciphertexts) {
            txs += rlp::encode_string2(ct);
        }
        byte_string body;
        body += rlp::encode_block_header(header);
        body += rlp::encode_list2(txs);
        body += rlp::encode_list2(); // ommers
        return rlp::encode_list2(body);
    }

    /// Each transaction's canonical leaf -- what decode_transaction accepts and
    /// what the plaintext walk would have captured -- encrypted.
    std::vector<byte_string> encrypt_transactions(
        L2CipherContext const &ctx, std::vector<Transaction> const &txs)
    {
        std::vector<byte_string> out;
        for (size_t i = 0; i < txs.size(); ++i) {
            std::array<unsigned char, 16> nonce{};
            nonce[0] = static_cast<unsigned char>(i);
            auto const plain = rlp::encode_transaction(txs[i]);
            std::vector<unsigned char> leaf;
            MONAD_ASSERT(l2_encrypt_leaf(
                ctx,
                sender_r(),
                nonce,
                std::span<unsigned char const>{plain.data(), plain.size()},
                leaf));
            out.emplace_back(leaf.begin(), leaf.end());
        }
        return out;
    }
}

// bind_secret is the whole reason decode_block_l2 can take a Secret and ask no
// questions. Two ways it must refuse: a scalar that is not the operator's, and
// one that is not a scalar at all.
TEST(DecodeBlockL2, BindSecretRefusesAnythingButTheOperatorKey)
{
    auto const ctx = context();
    auto const be = operator_sk_be();
    EXPECT_TRUE(
        L2Cipher::bind_secret(ctx, std::span<unsigned char const, 32>{be})
            .has_value());

    auto wrong = be;
    wrong[31] ^= 1u;
    EXPECT_FALSE(
        L2Cipher::bind_secret(ctx, std::span<unsigned char const, 32>{wrong})
            .has_value())
        << "a different scalar derives a different public key";

    std::array<unsigned char, 32> const zero{};
    EXPECT_FALSE(
        L2Cipher::bind_secret(ctx, std::span<unsigned char const, 32>{zero})
            .has_value())
        << "zero is not a valid scalar";

    std::array<unsigned char, 32> over{};
    for (auto &b : over) {
        b = 0xff;
    }
    EXPECT_FALSE(
        L2Cipher::bind_secret(ctx, std::span<unsigned char const, 32>{over})
            .has_value())
        << "at or above the group order is not a valid scalar";
}

TEST(DecodeBlockL2, RoundTripsEveryTransaction)
{
    auto const ctx = context();
    auto const secret = bound_secret(ctx);
    auto const original = sample_block();
    auto const cts = encrypt_transactions(ctx, original.transactions);
    auto const encoded = encode_l2_block(original.header, cts);

    byte_string_view view{encoded};
    std::vector<byte_string_view> ciphertexts;
    auto const got = decode_block_l2(view, ctx, secret, ciphertexts);
    ASSERT_FALSE(got.has_error());
    EXPECT_TRUE(view.empty());

    EXPECT_EQ(ciphertexts.size(), original.transactions.size());
    ASSERT_EQ(got.value().transactions.size(), original.transactions.size());
    for (size_t i = 0; i < original.transactions.size(); ++i) {
        EXPECT_EQ(got.value().transactions[i], original.transactions[i])
            << "tx " << i;
    }
}

// The divergence guard. Header, ommers and withdrawals must come out the same
// as rlp::decode_block gives on the plaintext block.
TEST(DecodeBlockL2, AgreesWithDecodeBlockOnEverythingElse)
{
    auto const ctx = context();
    auto const secret = bound_secret(ctx);
    auto const original = sample_block();

    auto const plain_rlp = rlp::encode_block(original);
    byte_string_view plain_view{plain_rlp};
    auto const plain = rlp::decode_block(plain_view);
    ASSERT_FALSE(plain.has_error());

    auto const cts = encrypt_transactions(ctx, original.transactions);
    auto const l2_rlp = encode_l2_block(original.header, cts);
    byte_string_view l2_view{l2_rlp};
    std::vector<byte_string_view> ciphertexts;
    auto const l2 = decode_block_l2(l2_view, ctx, secret, ciphertexts);
    ASSERT_FALSE(l2.has_error());

    EXPECT_EQ(l2.value().header, plain.value().header);
    EXPECT_EQ(l2.value().ommers, plain.value().ommers);
    EXPECT_EQ(l2.value().withdrawals, plain.value().withdrawals);
    EXPECT_EQ(l2.value().transactions, plain.value().transactions);
}

// The transactions root is taken over these, so they must be views into the
// input covering every leaf -- including the ones that get rejected.
TEST(DecodeBlockL2, CiphertextsAreViewsCoveringEveryLeaf)
{
    auto const ctx = context();
    auto const secret = bound_secret(ctx);
    auto const original = sample_block();
    auto const cts = encrypt_transactions(ctx, original.transactions);
    auto const encoded = encode_l2_block(original.header, cts);

    byte_string_view view{encoded};
    std::vector<byte_string_view> ciphertexts;
    ASSERT_FALSE(decode_block_l2(view, ctx, secret, ciphertexts).has_error());

    ASSERT_EQ(ciphertexts.size(), cts.size());
    for (size_t i = 0; i < cts.size(); ++i) {
        EXPECT_EQ(ciphertexts[i], byte_string_view{cts[i]}) << "leaf " << i;
        // Inside the encoded block, not a copy.
        EXPECT_GE(ciphertexts[i].data(), encoded.data());
        EXPECT_LE(
            ciphertexts[i].data() + ciphertexts[i].size(),
            encoded.data() + encoded.size());
    }
}

// A tampered leaf is CONSUMED, not fatal: it stays in the root's operand and
// simply produces no transaction. This is the protocol's rejection rule, and
// it is the reason the two vectors can differ in length.
TEST(DecodeBlockL2, TamperedLeafIsRejectedNotFatal)
{
    auto const ctx = context();
    auto const secret = bound_secret(ctx);
    auto const original = sample_block();
    auto cts = encrypt_transactions(ctx, original.transactions);
    cts[1].back() ^= 1u; // break the middle leaf's tag
    auto const encoded = encode_l2_block(original.header, cts);

    byte_string_view view{encoded};
    std::vector<byte_string_view> ciphertexts;
    auto const got = decode_block_l2(view, ctx, secret, ciphertexts);
    ASSERT_FALSE(got.has_error());

    EXPECT_EQ(ciphertexts.size(), 3u);
    ASSERT_EQ(got.value().transactions.size(), 2u);
    EXPECT_EQ(ciphertexts.size() - got.value().transactions.size(), 1u);
    // The survivors are the first and the third, in order.
    EXPECT_EQ(got.value().transactions[0], original.transactions[0]);
    EXPECT_EQ(got.value().transactions[1], original.transactions[2]);
}

// A leaf that decrypts to bytes that are not exactly one transaction is
// rejected the same way. Per-leaf framing is what makes this detectable at
// all: in the plaintext walk a short declared length desynchronises the walk.
TEST(DecodeBlockL2, TrailingBytesInAPlaintextAreRejected)
{
    auto const ctx = context();
    auto const secret = bound_secret(ctx);
    auto original = sample_block();
    original.transactions.resize(1);

    auto plain = rlp::encode_transaction(original.transactions[0]);
    plain.push_back(0x00); // one byte too many

    std::array<unsigned char, 16> const nonce{};
    std::vector<unsigned char> leaf;
    ASSERT_TRUE(l2_encrypt_leaf(
        ctx,
        sender_r(),
        nonce,
        std::span<unsigned char const>{plain.data(), plain.size()},
        leaf));

    auto const encoded = encode_l2_block(
        original.header, {byte_string{leaf.begin(), leaf.end()}});
    byte_string_view view{encoded};
    std::vector<byte_string_view> ciphertexts;
    auto const got = decode_block_l2(view, ctx, secret, ciphertexts);
    ASSERT_FALSE(got.has_error());
    EXPECT_EQ(ciphertexts.size(), 1u);
    EXPECT_TRUE(got.value().transactions.empty());
}

TEST(DecodeBlockL2, EmptyTransactionListIsFine)
{
    auto const ctx = context();
    auto const secret = bound_secret(ctx);
    BlockHeader header{};
    header.number = 9;
    auto const encoded = encode_l2_block(header, {});

    byte_string_view view{encoded};
    std::vector<byte_string_view> ciphertexts;
    auto const got = decode_block_l2(view, ctx, secret, ciphertexts);
    ASSERT_FALSE(got.has_error());
    EXPECT_TRUE(ciphertexts.empty());
    EXPECT_TRUE(got.value().transactions.empty());
}
