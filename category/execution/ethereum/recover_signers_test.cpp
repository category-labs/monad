// Copyright (C) 2025-26 Category Labs, Inc.
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

#include <category/core/address.hpp>
#include <category/core/assert.h>
#include <category/core/byte_string.hpp>
#include <category/core/bytes.hpp>
#include <category/core/fiber/priority_pool.hpp>
#include <category/core/int.hpp>
#include <category/core/keccak.hpp>
#include <category/execution/ethereum/core/ecrecover.hpp>
#include <category/execution/ethereum/core/ecrecover/impl.hpp>
#include <category/execution/ethereum/core/rlp/transaction_rlp.hpp>
#include <category/execution/ethereum/core/signature.hpp>
#include <category/execution/ethereum/core/transaction.hpp>
#include <category/execution/ethereum/execute_block.hpp>

#include <secp256k1.h>
#include <secp256k1_recovery.h>

#include <gtest/gtest.h>

#include <cstddef>
#include <cstdint>
#include <cstring>
#include <map>
#include <memory>
#include <optional>
#include <span>
#include <utility>
#include <vector>

using namespace monad;

namespace
{
    secp256k1_context const *signing_context()
    {
        static std::unique_ptr<
            secp256k1_context,
            void (*)(secp256k1_context *)> const context{
            secp256k1_context_create(
                SECP256K1_CONTEXT_SIGN | SECP256K1_CONTEXT_VERIFY),
            &secp256k1_context_destroy};
        return context.get();
    }

    // A distinct, valid secret key per `n`
    bytes32_t secret_key(uint64_t const n)
    {
        bytes32_t key{};
        store_be(key.bytes + 24, n + 1);
        return key;
    }

    Address address_of(bytes32_t const &key)
    {
        secp256k1_pubkey pubkey;
        MONAD_ASSERT(
            secp256k1_ec_pubkey_create(signing_context(), &pubkey, key.bytes));
        unsigned char serialized[65];
        size_t len = sizeof(serialized);
        MONAD_ASSERT(secp256k1_ec_pubkey_serialize(
            signing_context(),
            serialized,
            &len,
            &pubkey,
            SECP256K1_EC_UNCOMPRESSED));
        auto const hash = keccak256({serialized + 1, 64});
        Address address;
        std::memcpy(address.bytes, hash.bytes + 12, sizeof(address.bytes));
        return address;
    }

    Secp256k1Signature
    sign(byte_string_view const encoding, bytes32_t const &key)
    {
        auto const digest = keccak256(encoding);
        secp256k1_ecdsa_recoverable_signature sig;
        MONAD_ASSERT(secp256k1_ecdsa_sign_recoverable(
            signing_context(),
            &sig,
            digest.bytes,
            key.bytes,
            nullptr,
            nullptr));
        unsigned char compact[64];
        int recid;
        secp256k1_ecdsa_recoverable_signature_serialize_compact(
            signing_context(), compact, &recid, &sig);
        return Secp256k1Signature{
            .r = load_be_unsafe<uint256_t>(compact),
            .s = load_be_unsafe<uint256_t>(compact + 32),
            .y_parity = static_cast<uint8_t>(recid)};
    }

    // An r in [1, n) that is not the x-coordinate of a curve point, so
    // recovery with it fails even though the signature is well-formed
    uint256_t const &unrecoverable_r()
    {
        static uint256_t const r = [] {
            RecoverAddressInput input{};
            input.sig[63] = 1; // s = 1
            uint64_t x = 1;
            for (; x < 1000; ++x) {
                store_be(input.sig + 24, x);
                uint8_t out[20];
                if (!recover_address(out, input.msg, input.sig, 0)) {
                    break;
                }
            }
            MONAD_ASSERT(x < 1000);
            return uint256_t{x};
        }();
        return r;
    }

    // Kinds of damage applied to a signature after signing
    enum class Damage
    {
        none,
        zero_s, // out of range: no signer
        high_s, // malleable (EIP-2): no signer
        bad_y_parity, // y_parity > 1: no signer
        flipped_y_parity, // recovers a different, unrelated address
        unrecoverable_r, // well-formed, but ECDSA recovery fails
    };

    void damage(Secp256k1Signature &sig, Damage const kind)
    {
        switch (kind) {
        case Damage::none:
            break;
        case Damage::zero_s:
            sig.s = 0;
            break;
        case Damage::high_s:
            sig.s = Secp256k1Signature::secp256k1_order - sig.s;
            break;
        case Damage::bad_y_parity:
            sig.y_parity = 2;
            break;
        case Damage::flipped_y_parity:
            sig.y_parity ^= 1;
            break;
        case Damage::unrecoverable_r:
            sig.r = unrecoverable_r();
            break;
        }
    }

    Damage damage_for(uint64_t const n)
    {
        // Mostly intact signatures, with every kind of damage represented
        switch (n % 11) {
        case 3:
            return Damage::zero_s;
        case 5:
            return Damage::high_s;
        case 6:
            return Damage::bad_y_parity;
        case 8:
            return Damage::flipped_y_parity;
        case 9:
            return Damage::unrecoverable_r;
        default:
            return Damage::none;
        }
    }

    struct SignedBlock
    {
        std::vector<Transaction> transactions;
        // Signers of the undamaged signatures, keyed by (tx, slot) where slot
        // 0 is the sender and slot j > 0 authorization entry j - 1
        std::map<std::pair<size_t, size_t>, Address> signers;
    };

    // A mix of legacy, EIP-1559 and EIP-7702 transactions, the latter with
    // 0 to 3 authorization entries, so batch boundaries fall both between
    // and inside transactions
    SignedBlock make_block(size_t const num_transactions)
    {
        SignedBlock block;
        uint64_t key_index = 0;
        for (size_t i = 0; i < num_transactions; ++i) {
            Transaction tx{};
            tx.nonce = i;
            tx.gas_limit = 21'000 + i;
            tx.max_fee_per_gas = 1'000'000'000;
            tx.value = i;
            tx.to = Address{};
            tx.data = byte_string(i % 70, static_cast<unsigned char>(i));
            tx.sc.chain_id = 143;
            switch (i % 3) {
            case 0:
                tx.type = TransactionType::legacy;
                break;
            case 1:
                tx.type = TransactionType::eip1559;
                tx.max_priority_fee_per_gas = 1'000;
                break;
            default:
                tx.type = TransactionType::eip7702;
                tx.max_priority_fee_per_gas = 1'000;
                for (size_t j = 0; j < (i / 3) % 4; ++j) {
                    AuthorizationEntry entry{};
                    entry.sc.chain_id = 143;
                    entry.address.bytes[19] = static_cast<uint8_t>(j);
                    entry.nonce = i * 4 + j;
                    auto const key = secret_key(key_index++);
                    entry.sc.signature = sign(
                        rlp::encode_authorization_entry_for_signing(entry),
                        key);
                    Damage const kind = damage_for(key_index);
                    damage(entry.sc.signature, kind);
                    if (kind == Damage::none) {
                        block.signers[{i, j + 1}] = address_of(key);
                    }
                    tx.authorization_list.push_back(entry);
                }
                break;
            }
            auto const key = secret_key(key_index++);
            tx.sc.signature =
                sign(rlp::encode_transaction_for_signing(tx), key);
            Damage const kind = damage_for(key_index);
            damage(tx.sc.signature, kind);
            if (kind == Damage::none) {
                block.signers[{i, 0}] = address_of(key);
            }
            block.transactions.push_back(std::move(tx));
        }
        return block;
    }
}

TEST(RecoverAddresses, matches_recover_address)
{
    std::vector<RecoverAddressInput> inputs;
    for (uint64_t n = 0; n < 40; ++n) {
        Transaction tx{};
        tx.nonce = n;
        tx.sc.chain_id = 1;
        auto const encoding = rlp::encode_transaction_for_signing(tx);
        auto sig = sign(encoding, secret_key(n));
        // Only damage that keeps the signature well-formed reaches
        // recover_addresses: the malformed kinds have no input at all
        if (n % 4 == 1) {
            damage(sig, Damage::unrecoverable_r);
        }
        else if (n % 4 == 2) {
            damage(sig, Damage::flipped_y_parity);
        }
        auto const input = make_recover_address_input(sig, encoding);
        ASSERT_TRUE(input.has_value());
        inputs.push_back(*input);
    }

    for (size_t const size : {0uz, 1uz, 7uz, 8uz, 9uz, inputs.size()}) {
        SCOPED_TRACE(size);
        std::span<RecoverAddressInput const> const in{inputs.data(), size};
        std::vector<RecoverAddressOutput> out(size);
        recover_addresses(in, out);
        for (size_t i = 0; i < size; ++i) {
            uint8_t expected[20];
            bool const expected_ok =
                recover_address(expected, in[i].msg, in[i].sig, in[i].recid);
            ASSERT_EQ(out[i].ok, expected_ok) << i;
            if (expected_ok) {
                EXPECT_EQ(0, std::memcmp(out[i].address, expected, 20)) << i;
            }
        }
    }
}

TEST(RecoverSigners, empty_block)
{
    fiber::PriorityPool pool{2, 4};
    auto const signers = recover_signers({}, pool);
    EXPECT_TRUE(signers.senders.empty());
    EXPECT_TRUE(signers.authorities.empty());
}

TEST(RecoverSigners, matches_scalar_recovery)
{
    for (size_t const num_transactions :
         {1uz, 2uz, 7uz, 8uz, 9uz, 31uz, 33uz, 100uz, 257uz, 1000uz}) {
        SignedBlock const block = make_block(num_transactions);
        auto const &transactions = block.transactions;

        // Scalar recovery is the reference; it must also agree with the
        // signing keys wherever the signature was left intact
        std::vector<std::optional<Address>> expected_senders;
        std::vector<std::vector<std::optional<Address>>> expected_authorities;
        size_t num_failures = 0;
        for (Transaction const &transaction : transactions) {
            expected_senders.push_back(recover_sender(transaction));
            num_failures += !expected_senders.back().has_value();
            auto &auths = expected_authorities.emplace_back();
            for (auto const &entry : transaction.authorization_list) {
                auths.push_back(recover_authority(entry));
                num_failures += !auths.back().has_value();
            }
        }
        for (auto const &[slot, signer] : block.signers) {
            auto const &[i, j] = slot;
            auto const &recovered =
                j == 0 ? expected_senders[i] : expected_authorities[i][j - 1];
            ASSERT_EQ(recovered, signer) << i << " " << j;
        }
        if (num_transactions >= 100) {
            ASSERT_GT(num_failures, 0u);
        }

        for (unsigned const num_threads : {1u, 2u, 4u}) {
            SCOPED_TRACE(
                testing::Message() << num_transactions << " transactions, "
                                   << num_threads << " threads");
            fiber::PriorityPool pool{num_threads, 8};
            auto const signers = recover_signers(transactions, pool);
            EXPECT_EQ(signers.senders, expected_senders);
            EXPECT_EQ(signers.authorities, expected_authorities);
        }
    }
}
