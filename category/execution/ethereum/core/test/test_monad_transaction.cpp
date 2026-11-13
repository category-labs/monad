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

#include <category/core/hex.hpp>
#include <category/core/keccak.hpp>
#include <category/execution/ethereum/core/receipt.hpp>
#include <category/execution/ethereum/core/rlp/receipt_rlp.hpp>
#include <category/execution/ethereum/core/rlp/transaction_rlp.hpp>
#include <category/execution/ethereum/core/transaction.hpp>
#include <category/execution/ethereum/rlp/decode.hpp>
#include <category/execution/ethereum/rlp/encode2.hpp>

#include <gtest/gtest.h>
#include <nlohmann/json.hpp>

#include <filesystem>
#include <fstream>

using namespace monad;

namespace
{
    nlohmann::json vectors()
    {
        std::ifstream input(
            std::filesystem::path{__FILE__}.parent_path() /
            "monad_type40_vectors.json");
        return nlohmann::json::parse(input)["vectors"];
    }

    byte_string field(nlohmann::json const &vector, char const *key)
    {
        return from_hex(vector[key].get<std::string>()).value();
    }

    byte_string string_frame(size_t length, byte_string_view payload)
    {
        byte_string out;
        if (length <= 55) {
            out.push_back(0x80 + static_cast<unsigned char>(length));
        }
        else {
            auto const size = rlp::to_big_compact(length);
            out.push_back(0xb7 + static_cast<unsigned char>(size.size()));
            out += size;
        }
        out += payload;
        return out;
    }
}

TEST(MonadTransaction, BlockItemsRequireExactStringFraming)
{
    for (auto const &vector : vectors()) {
        SCOPED_TRACE(vector["name"].get<std::string>());
        auto const canonical = field(vector, "canonical");
        auto const wrapped = rlp::encode_string2(canonical);
        Transaction const legacy{};
        auto const legacy_bytes = rlp::encode_transaction(legacy);
        auto const valid_list =
            rlp::encode_list2(legacy_bytes, wrapped, wrapped);
        byte_string_view view{valid_list};
        auto const decoded = rlp::decode_transaction_list(view);
        ASSERT_TRUE(decoded.has_value());
        ASSERT_TRUE(view.empty());
        ASSERT_EQ(decoded.value().size(), 3);
        EXPECT_EQ(rlp::encode_transaction(decoded.value()[0]), legacy_bytes);
        EXPECT_EQ(rlp::encode_transaction(decoded.value()[1]), canonical);
        EXPECT_EQ(rlp::encode_transaction(decoded.value()[2]), canonical);

        auto reject = [&](byte_string const &item) {
            // Include a following transaction so decoders cannot borrow its
            // bytes.
            auto const list = rlp::encode_list2(item, wrapped);
            byte_string_view input{list};
            EXPECT_FALSE(rlp::decode_transaction_list(input).has_value());
        };
        reject(canonical);
        for (size_t length = 0; length <= canonical.size() + 1; ++length) {
            if (length != canonical.size()) {
                reject(string_frame(length, canonical));
            }
        }
        reject(rlp::encode_string2(canonical + byte_string{0x80}));
        reject(rlp::encode_string2(wrapped));
    }
}

TEST(MonadTransaction, SdkVectorsPreserveCanonicalIdentityAndRecoverSender)
{
    for (auto const &vector : vectors()) {
        SCOPED_TRACE(vector["name"].get<std::string>());
        auto const canonical = field(vector, "canonical");
        byte_string_view view{canonical};
        auto const decoded = rlp::decode_transaction(view);
        ASSERT_TRUE(decoded.has_value());
        ASSERT_TRUE(view.empty());
        auto const &tx = decoded.value();
        EXPECT_EQ(tx.type, TransactionType::monad);
        EXPECT_EQ(rlp::encode_transaction(tx), canonical);
        EXPECT_EQ(
            "0x" + to_hex(keccak256(canonical)),
            vector["hash"].get<std::string>());
        EXPECT_EQ(
            rlp::encode_transaction_for_signing(tx),
            field(vector, "signingPayload"));
        EXPECT_EQ(
            "0x" + to_hex(keccak256(rlp::encode_transaction_for_signing(tx))),
            vector["signingHash"].get<std::string>());
        auto const sender = recover_sender(tx);
        ASSERT_TRUE(sender.has_value());
        EXPECT_EQ("0x" + to_hex(*sender), vector["sender"].get<std::string>());

        auto const submission = field(vector, "submission");
        view = submission;
        EXPECT_FALSE(rlp::decode_transaction(view).has_value());
        EXPECT_NE(to_hex(keccak256(canonical)), to_hex(keccak256(submission)));
        for (size_t len = 0; len < canonical.size(); ++len) {
            view = byte_string_view{canonical}.substr(0, len);
            EXPECT_FALSE(rlp::decode_transaction(view).has_value());
        }
    }
}

TEST(MonadTransaction, SignatureMalleabilityIsRejectedWithoutRewritingBytes)
{
    auto const canonical = field(vectors()[1], "canonical");
    byte_string_view view{canonical};
    auto tx = rlp::decode_transaction(view).value();
    tx.sc.signature.s =
        0xfffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141_u256 -
        tx.sc.signature.s;
    tx.sc.signature.y_parity ^= 1;
    auto const malleated = rlp::encode_transaction(tx);
    view = malleated;
    auto const decoded = rlp::decode_transaction(view);
    ASSERT_TRUE(decoded.has_value());
    EXPECT_EQ(rlp::encode_transaction(decoded.value()), malleated);
    EXPECT_FALSE(recover_sender(decoded.value()).has_value());
    EXPECT_NE(to_hex(keccak256(canonical)), to_hex(keccak256(malleated)));
}

TEST(MonadTransaction, EmptyAccessListPresenceSurvivesProjection)
{
    auto const absent = field(vectors()[1], "canonical");
    auto const empty = field(vectors()[2], "canonical");
    byte_string_view absent_view{absent};
    byte_string_view empty_view{empty};
    auto const a = rlp::decode_transaction(absent_view).value();
    auto const b = rlp::decode_transaction(empty_view).value();
    EXPECT_TRUE(a.access_list.empty());
    EXPECT_TRUE(b.access_list.empty());
    EXPECT_FALSE(a.monad_access_list_present);
    EXPECT_TRUE(b.monad_access_list_present);
    EXPECT_NE(
        rlp::encode_transaction_for_signing(a),
        rlp::encode_transaction_for_signing(b));
    EXPECT_EQ(rlp::encode_transaction(a), absent);
    EXPECT_EQ(rlp::encode_transaction(b), empty);
}

TEST(MonadTransaction, RejectsMalformedFeaturesAndParentOverflow)
{
    auto const canonical = field(vectors()[1], "canonical");
    byte_string_view view{canonical};
    view.remove_prefix(1);
    auto payload = rlp::parse_list_metadata(view).value();
    auto const before_chain = payload;
    rlp::parse_string_metadata(payload).value();
    auto const chain =
        before_chain.substr(0, before_chain.size() - payload.size());
    auto feature_payload = rlp::parse_list_metadata(payload).value();
    std::vector<byte_string> features;
    while (!feature_payload.empty()) {
        auto const raw = rlp::parse_list_metadata_raw(feature_payload).value();
        features.emplace_back(raw);
    }
    auto reject = [&](std::vector<byte_string> const &items) {
        byte_string body;
        for (auto const &item : items) {
            body += item;
        }
        auto const raw =
            byte_string(1, 0x40) +
            rlp::encode_list2(byte_string{chain}, rlp::encode_list2(body));
        byte_string_view input{raw};
        EXPECT_FALSE(rlp::decode_transaction(input).has_value());
    };
    auto mutated = features;
    std::swap(mutated[0], mutated[1]);
    reject(mutated);
    mutated = features;
    mutated.insert(mutated.begin() + 1, mutated[0]);
    reject(mutated);
    mutated = features;
    mutated.erase(mutated.begin());
    reject(mutated);
    mutated = features;
    mutated.insert(mutated.begin() + 3, byte_string{0xc2, 0x05, 0xc0});
    reject(mutated);
    mutated = features;
    mutated[2] = byte_string{0xc3, 0x03, 0xf8, 0xff};
    reject(mutated);
    mutated = features;
    mutated[0] = byte_string{0xc2, 0x01, 0x00};
    reject(mutated);
}

TEST(MonadTransaction, ReceiptCommitsEmptyExtensionList)
{
    Receipt receipt;
    receipt.type = TransactionType::monad;
    receipt.status = 1;
    receipt.gas_used = 21000;
    auto const encoded = rlp::encode_receipt(receipt);
    byte_string_view view{encoded};
    auto const decoded = rlp::decode_receipt(view);
    ASSERT_TRUE(decoded.has_value());
    EXPECT_TRUE(view.empty());
    EXPECT_EQ(rlp::encode_receipt(decoded.value()), encoded);
    view = byte_string_view{encoded}.substr(1);
    auto payload = rlp::parse_list_metadata(view).value();
    EXPECT_EQ(payload.back(), 0xc0);
    payload.remove_suffix(1);
    auto const missing_extension =
        byte_string(1, 0x40) + rlp::encode_list2(byte_string{payload});
    view = missing_extension;
    EXPECT_FALSE(rlp::decode_receipt(view).has_value());
    auto const nonempty_extension =
        byte_string(1, 0x40) +
        rlp::encode_list2(byte_string{payload} + byte_string{0xc1, 0x80});
    view = nonempty_extension;
    EXPECT_FALSE(rlp::decode_receipt(view).has_value());
}
