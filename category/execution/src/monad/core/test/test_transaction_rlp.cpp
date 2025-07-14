#include <category/core/byte_string.hpp>
#include <monad/core/rlp/transaction_rlp.hpp>
#include <monad/core/transaction.hpp>

#include <evmc/evmc.hpp>

#include <intx/intx.hpp>

#include <gtest/gtest.h>

#include <cstddef>

using namespace monad;
using namespace monad::rlp;

TEST(Rlp_Transaction, DecodeEncodeAccessList)
{
    // Empty List
    monad::AccessList const a{};
    auto encoded_access_list1 = encode_access_list(a);
    auto const empty_access_list = monad::byte_string({0xc0});
    EXPECT_EQ(encoded_access_list1, empty_access_list);

    // Simple List
    monad::AccessList b{
        {0xf8636377b7a998b51a3cf2bd711b870b3ab0ad56_address,
         {0xbea34dd04b09ad3b6014251ee24578074087ee60fda8c391cf466dfe5d687d7b_bytes32}}};
    auto const encoded_access_list2 = encode_access_list(b);
    auto const access_list = monad::byte_string(
        {0xf8, 0x38, 0xf7, 0x94, 0xf8, 0x63, 0x63, 0x77, 0xb7, 0xa9, 0x98, 0xb5,
         0x1a, 0x3c, 0xf2, 0xbd, 0x71, 0x1b, 0x87, 0x0b, 0x3a, 0xb0, 0xad, 0x56,
         0xe1, 0xa0, 0xbe, 0xa3, 0x4d, 0xd0, 0x4b, 0x09, 0xad, 0x3b, 0x60, 0x14,
         0x25, 0x1e, 0xe2, 0x45, 0x78, 0x07, 0x40, 0x87, 0xee, 0x60, 0xfd, 0xa8,
         0xc3, 0x91, 0xcf, 0x46, 0x6d, 0xfe, 0x5d, 0x68, 0x7d, 0x7b});
    EXPECT_EQ(encoded_access_list2, access_list);

    byte_string_view encoded_access_list_view2{encoded_access_list2};
    auto const decoded_access_list2 =
        decode_access_list(encoded_access_list_view2);
    ASSERT_FALSE(decoded_access_list2.has_error());
    EXPECT_EQ(encoded_access_list_view2.size(), 0);

    EXPECT_EQ(decoded_access_list2.value()[0].a, b[0].a);
    EXPECT_EQ(decoded_access_list2.value()[0].keys[0], b[0].keys[0]);

    // More Complicated List
    static constexpr auto access_addr{
        0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0_address};
    static constexpr auto key1{
        0x0000000000000000000000000000000000000000000000000000000000000007_bytes32};
    static constexpr auto key2{
        0x0000000000000000000000000000000000000000000000000000000000000003_bytes32};
    static monad::AccessList const list{AccessEntry{access_addr, {key1, key2}}};
    auto const eip2930_example = monad::byte_string(
        {0xf8, 0x5b, 0xf8, 0x59, 0x94, 0xa0, 0xa0, 0xa0, 0xa0, 0xa0, 0xa0, 0xa0,
         0xa0, 0xa0, 0xa0, 0xa0, 0xa0, 0xa0, 0xa0, 0xa0, 0xa0, 0xa0, 0xa0, 0xa0,
         0xa0, 0xf8, 0x42, 0xa0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
         0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
         0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x07,
         0xa0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
         0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
         0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x03});

    auto const encoded_access_list3 = encode_access_list(list);
    EXPECT_EQ(encoded_access_list3, eip2930_example);

    byte_string_view encoded_access_list_view3{encoded_access_list3};
    auto const decoded_access_list3 =
        decode_access_list(encoded_access_list_view3);
    ASSERT_FALSE(decoded_access_list3.has_error());
    EXPECT_EQ(encoded_access_list_view3.size(), 0);

    EXPECT_EQ(decoded_access_list3.value()[0].a, list[0].a);
    EXPECT_EQ(decoded_access_list3.value()[0].keys, list[0].keys);
}

TEST(Rlp_Transaction, EncodeAccessListMultipleEntry)
{
    auto const access_list = AccessList{
        AccessEntry{
            .a = 0xcccccccccccccccccccccccccccccccccccccccc_address,
            .keys =
                {0x000000000000000000000000000000000000000000000000000000000000ce11_bytes32}},
        AccessEntry{
            .a = 0xcccccccccccccccccccccccccccccccccccccccf_address,
            .keys = {
                0x00000000000000000000000000000000000000000000000000000000000060a7_bytes32}}};
    auto const expected = byte_string{
        0xf8, 0x70, 0xf7, 0x94, 0xcc, 0xcc, 0xcc, 0xcc, 0xcc, 0xcc, 0xcc, 0xcc,
        0xcc, 0xcc, 0xcc, 0xcc, 0xcc, 0xcc, 0xcc, 0xcc, 0xcc, 0xcc, 0xcc, 0xcc,
        0xe1, 0xa0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xce, 0x11, 0xf7, 0x94,
        0xcc, 0xcc, 0xcc, 0xcc, 0xcc, 0xcc, 0xcc, 0xcc, 0xcc, 0xcc, 0xcc, 0xcc,
        0xcc, 0xcc, 0xcc, 0xcc, 0xcc, 0xcc, 0xcc, 0xcf, 0xe1, 0xa0, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x00, 0x60, 0xa7};
    EXPECT_EQ(encode_access_list(access_list), expected);
}

// Example data from: EIP-155
TEST(Rlp_Transaction, DecodeEncodeLegacy)
{
    using namespace intx;
    using namespace evmc::literals;

    static constexpr auto price{20'000'000'000};
    static constexpr auto value{0xde0b6b3a7640000_u256};
    static constexpr auto to_addr{
        0x3535353535353535353535353535353535353535_address};
    static constexpr auto r{
        0x28ef61340bd939bc2195fe537567866003e1a15d3c71ff63e1590620aa636276_u256};
    static constexpr auto s{
        0x67cbe9d8997f761aecb703304b3800ccf555c9f3dc64214b297fb1966a3b6d83_u256};

    monad::Transaction const t{
        .sc = {.r = r, .s = s}, // no chain_id in legacy transactions
        .nonce = 9,
        .max_fee_per_gas = price,
        .gas_limit = 21'000,
        .value = value,
        .to = to_addr};
    monad::byte_string const legacy_transaction{
        0xf8, 0x6c, 0x09, 0x85, 0x04, 0xa8, 0x17, 0xc8, 0x00, 0x82, 0x52,
        0x08, 0x94, 0x35, 0x35, 0x35, 0x35, 0x35, 0x35, 0x35, 0x35, 0x35,
        0x35, 0x35, 0x35, 0x35, 0x35, 0x35, 0x35, 0x35, 0x35, 0x35, 0x35,
        0x88, 0x0d, 0xe0, 0xb6, 0xb3, 0xa7, 0x64, 0x00, 0x00, 0x80, 0x1b,
        0xa0, 0x28, 0xef, 0x61, 0x34, 0x0b, 0xd9, 0x39, 0xbc, 0x21, 0x95,
        0xfe, 0x53, 0x75, 0x67, 0x86, 0x60, 0x03, 0xe1, 0xa1, 0x5d, 0x3c,
        0x71, 0xff, 0x63, 0xe1, 0x59, 0x06, 0x20, 0xaa, 0x63, 0x62, 0x76,
        0xa0, 0x67, 0xcb, 0xe9, 0xd8, 0x99, 0x7f, 0x76, 0x1a, 0xec, 0xb7,
        0x03, 0x30, 0x4b, 0x38, 0x00, 0xcc, 0xf5, 0x55, 0xc9, 0xf3, 0xdc,
        0x64, 0x21, 0x4b, 0x29, 0x7f, 0xb1, 0x96, 0x6a, 0x3b, 0x6d, 0x83};
    auto const legacy_rlp_transaction = encode_transaction(t);
    EXPECT_EQ(legacy_rlp_transaction, legacy_transaction);

    byte_string_view encoded_transaction_view{legacy_rlp_transaction};
    auto const decoded_transaction =
        decode_transaction(encoded_transaction_view);
    ASSERT_FALSE(decoded_transaction.has_error());
    EXPECT_EQ(encoded_transaction_view.size(), 0);

    EXPECT_EQ(decoded_transaction.value().nonce, t.nonce);
    EXPECT_EQ(decoded_transaction.value().max_fee_per_gas, t.max_fee_per_gas);
    EXPECT_EQ(decoded_transaction.value().gas_limit, t.gas_limit);
    EXPECT_EQ(decoded_transaction.value().value, t.value);
    EXPECT_EQ(*decoded_transaction.value().to, *t.to);
    EXPECT_EQ(decoded_transaction.value().to.value(), t.to.value());
    EXPECT_EQ(decoded_transaction.value().sc.r, t.sc.r);
    EXPECT_EQ(decoded_transaction.value().sc.s, t.sc.s);
}

TEST(Rlp_Transaction, DecodeEncodeLegacyNoTo)
{
    using namespace intx;
    using namespace evmc::literals;

    static constexpr auto price{20'000'000'000};
    static constexpr auto value{0xde0b6b3a7640000_u256};
    static constexpr auto r{
        0x28ef61340bd939bc2195fe537567866003e1a15d3c71ff63e1590620aa636276_u256};
    static constexpr auto s{
        0x67cbe9d8997f761aecb703304b3800ccf555c9f3dc64214b297fb1966a3b6d83_u256};

    monad::Transaction const t{
        .sc = {.r = r, .s = s}, // no chain_id in legacy transactions
        .nonce = 9,
        .max_fee_per_gas = price,
        .gas_limit = 21'000,
        .value = value};

    auto const legacy_rlp_transaction = encode_transaction(t);

    byte_string_view encoded_transaction_view{legacy_rlp_transaction};
    auto const decoded_transaction =
        decode_transaction(encoded_transaction_view);
    ASSERT_FALSE(decoded_transaction.has_error());
    EXPECT_EQ(encoded_transaction_view.size(), 0);

    EXPECT_EQ(decoded_transaction.value().nonce, t.nonce);
    EXPECT_EQ(decoded_transaction.value().max_fee_per_gas, t.max_fee_per_gas);
    EXPECT_EQ(decoded_transaction.value().gas_limit, t.gas_limit);
    EXPECT_EQ(decoded_transaction.value().value, t.value);
    EXPECT_EQ(decoded_transaction.value().to.has_value(), false);
    EXPECT_EQ(decoded_transaction.value().sc.r, t.sc.r);
    EXPECT_EQ(decoded_transaction.value().sc.s, t.sc.s);
}

TEST(Rlp_Transaction, EncodeEip155)
{
    using namespace intx;
    using namespace evmc::literals;

    static constexpr auto price{20'000'000'000};
    static constexpr auto value{0xde0b6b3a7640000_u256};
    static constexpr auto to_addr{
        0x3535353535353535353535353535353535353535_address};
    static constexpr auto r{
        0x28ef61340bd939bc2195fe537567866003e1a15d3c71ff63e1590620aa636276_u256};
    static constexpr auto s{
        0x67cbe9d8997f761aecb703304b3800ccf555c9f3dc64214b297fb1966a3b6d83_u256};

    monad::Transaction const t{
        .sc = {.r = r, .s = s, .chain_id = 5}, // Goerli
        .nonce = 9,
        .max_fee_per_gas = price,
        .gas_limit = 21'000,
        .value = value,
        .to = to_addr};
    monad::byte_string const eip155_transaction{
        0xf8, 0x6c, 0x09, 0x85, 0x04, 0xa8, 0x17, 0xc8, 0x00, 0x82, 0x52,
        0x08, 0x94, 0x35, 0x35, 0x35, 0x35, 0x35, 0x35, 0x35, 0x35, 0x35,
        0x35, 0x35, 0x35, 0x35, 0x35, 0x35, 0x35, 0x35, 0x35, 0x35, 0x35,
        0x88, 0x0d, 0xe0, 0xb6, 0xb3, 0xa7, 0x64, 0x00, 0x00, 0x80, 0x2d,
        0xa0, 0x28, 0xef, 0x61, 0x34, 0x0b, 0xd9, 0x39, 0xbc, 0x21, 0x95,
        0xfe, 0x53, 0x75, 0x67, 0x86, 0x60, 0x03, 0xe1, 0xa1, 0x5d, 0x3c,
        0x71, 0xff, 0x63, 0xe1, 0x59, 0x06, 0x20, 0xaa, 0x63, 0x62, 0x76,
        0xa0, 0x67, 0xcb, 0xe9, 0xd8, 0x99, 0x7f, 0x76, 0x1a, 0xec, 0xb7,
        0x03, 0x30, 0x4b, 0x38, 0x00, 0xcc, 0xf5, 0x55, 0xc9, 0xf3, 0xdc,
        0x64, 0x21, 0x4b, 0x29, 0x7f, 0xb1, 0x96, 0x6a, 0x3b, 0x6d, 0x83};
    auto const eip155_rlp_transaction = encode_transaction(t);
    EXPECT_EQ(eip155_rlp_transaction, eip155_transaction);

    byte_string_view encoded_transaction_view{eip155_rlp_transaction};
    auto const decoded_transaction =
        decode_transaction(encoded_transaction_view);
    ASSERT_FALSE(decoded_transaction.has_error());
    EXPECT_EQ(encoded_transaction_view.size(), 0);

    EXPECT_EQ(decoded_transaction.value().nonce, t.nonce);
    EXPECT_EQ(decoded_transaction.value().max_fee_per_gas, t.max_fee_per_gas);
    EXPECT_EQ(decoded_transaction.value().gas_limit, t.gas_limit);
    EXPECT_EQ(decoded_transaction.value().value, t.value);
    EXPECT_EQ(*decoded_transaction.value().to, *t.to);
    EXPECT_EQ(decoded_transaction.value().to.value(), t.to.value());
    EXPECT_EQ(decoded_transaction.value().sc.r, t.sc.r);
    EXPECT_EQ(decoded_transaction.value().sc.s, t.sc.s);
    EXPECT_EQ(*decoded_transaction.value().sc.chain_id, *t.sc.chain_id);
    EXPECT_EQ(
        decoded_transaction.value().sc.chain_id.value(), t.sc.chain_id.value());
}

TEST(Rlp_Transaction, EncodeEip2930)
{
    using namespace intx;
    using namespace evmc::literals;

    static constexpr auto price{20'000'000'000};
    static constexpr auto value{0xde0b6b3a7640000_u256};
    static constexpr auto to_addr{
        0x3535353535353535353535353535353535353535_address};
    static constexpr auto access_addr{
        0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0_address};
    static constexpr auto r{
        0x28ef61340bd939bc2195fe537567866003e1a15d3c71ff63e1590620aa636276_u256};
    static constexpr auto s{
        0x67cbe9d8997f761aecb703304b3800ccf555c9f3dc64214b297fb1966a3b6d83_u256};
    static constexpr auto key1{
        0x0000000000000000000000000000000000000000000000000000000000000007_bytes32};
    static constexpr auto key2{
        0x0000000000000000000000000000000000000000000000000000000000000003_bytes32};
    static monad::AccessList const a{AccessEntry{access_addr, {key1, key2}}};

    monad::Transaction const t{
        .sc = {.r = r, .s = s, .chain_id = 3}, // Ropsten
        .nonce = 9,
        .max_fee_per_gas = price,
        .gas_limit = 21'000,
        .value = value,
        .to = to_addr,
        .type = monad::TransactionType::eip2930,
        .access_list = a};
    monad::byte_string const eip2930_transaction{
        0x01, 0xf8, 0xca, 0x03, 0x09, 0x85, 0x04, 0xa8, 0x17, 0xc8, 0x00, 0x82,
        0x52, 0x08, 0x94, 0x35, 0x35, 0x35, 0x35, 0x35, 0x35, 0x35, 0x35, 0x35,
        0x35, 0x35, 0x35, 0x35, 0x35, 0x35, 0x35, 0x35, 0x35, 0x35, 0x35, 0x88,
        0x0d, 0xe0, 0xb6, 0xb3, 0xa7, 0x64, 0x00, 0x00, 0x80,

        0xf8, 0x5b, 0xf8, 0x59, 0x94, 0xa0, 0xa0, 0xa0, 0xa0, 0xa0, 0xa0, 0xa0,
        0xa0, 0xa0, 0xa0, 0xa0, 0xa0, 0xa0, 0xa0, 0xa0, 0xa0, 0xa0, 0xa0, 0xa0,
        0xa0, 0xf8, 0x42, 0xa0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x07,
        0xa0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x03,

        0x80, 0xa0, 0x28, 0xef, 0x61, 0x34, 0x0b, 0xd9, 0x39, 0xbc, 0x21, 0x95,
        0xfe, 0x53, 0x75, 0x67, 0x86, 0x60, 0x03, 0xe1, 0xa1, 0x5d, 0x3c, 0x71,
        0xff, 0x63, 0xe1, 0x59, 0x06, 0x20, 0xaa, 0x63, 0x62, 0x76, 0xa0, 0x67,
        0xcb, 0xe9, 0xd8, 0x99, 0x7f, 0x76, 0x1a, 0xec, 0xb7, 0x03, 0x30, 0x4b,
        0x38, 0x00, 0xcc, 0xf5, 0x55, 0xc9, 0xf3, 0xdc, 0x64, 0x21, 0x4b, 0x29,
        0x7f, 0xb1, 0x96, 0x6a, 0x3b, 0x6d, 0x83};
    auto const eip2930_rlp_transaction = monad::rlp::encode_transaction(t);
    EXPECT_EQ(eip2930_rlp_transaction, eip2930_transaction);

    byte_string_view encoded_transaction_view{eip2930_rlp_transaction};
    auto const decoded_transaction =
        decode_transaction(encoded_transaction_view);
    ASSERT_FALSE(decoded_transaction.has_error());
    EXPECT_EQ(encoded_transaction_view.size(), 0);

    EXPECT_EQ(decoded_transaction.value().nonce, t.nonce);
    EXPECT_EQ(decoded_transaction.value().max_fee_per_gas, t.max_fee_per_gas);
    EXPECT_EQ(decoded_transaction.value().gas_limit, t.gas_limit);
    EXPECT_EQ(decoded_transaction.value().value, t.value);
    EXPECT_EQ(*decoded_transaction.value().to, *t.to);
    EXPECT_EQ(decoded_transaction.value().to.value(), t.to.value());
    EXPECT_EQ(decoded_transaction.value().sc.r, t.sc.r);
    EXPECT_EQ(decoded_transaction.value().sc.s, t.sc.s);
    EXPECT_EQ(*decoded_transaction.value().sc.chain_id, *t.sc.chain_id);
    EXPECT_EQ(
        decoded_transaction.value().sc.chain_id.value(), t.sc.chain_id.value());
    EXPECT_EQ(decoded_transaction.value().type, t.type);

    EXPECT_EQ(
        decoded_transaction.value().access_list.size(), t.access_list.size());

    for (size_t i = 0u; i < t.access_list.size(); ++i) {
        EXPECT_EQ(
            decoded_transaction.value().access_list[i].a, t.access_list[i].a);
        EXPECT_EQ(
            decoded_transaction.value().access_list[i].keys.size(),
            t.access_list[i].keys.size());
        EXPECT_EQ(
            decoded_transaction.value().access_list[i].keys,
            t.access_list[i].keys);
    }
}

TEST(Rlp_Transaction, EncodeEip1559TrueParity)
{
    using namespace intx;
    using namespace evmc::literals;

    static constexpr auto price{20'000'000'000};
    static constexpr auto value{0xde0b6b3a7640000_u256};
    static constexpr auto tip{4'000'000'000};
    static constexpr auto to_addr{
        0x3535353535353535353535353535353535353535_address};
    static constexpr auto r{
        0x28ef61340bd939bc2195fe537567866003e1a15d3c71ff63e1590620aa636276_u256};
    static constexpr auto s{
        0x67cbe9d8997f761aecb703304b3800ccf555c9f3dc64214b297fb1966a3b6d83_u256};
    static monad::AccessList const a{};

    monad::Transaction const t{
        .sc = {.r = r, .s = s, .chain_id = 137, .y_parity = true}, // Polygon
        .nonce = 9,
        .max_fee_per_gas = price,
        .gas_limit = 21'000,
        .value = value,
        .to = to_addr,
        .type = monad::TransactionType::eip1559,
        .access_list = a,
        .max_priority_fee_per_gas = tip};
    monad::byte_string const eip1559_transaction{
        0x02, 0xf8, 0x74, 0x81, 0x89, 0x09, 0x84, 0xee, 0x6b, 0x28, 0x00, 0x85,
        0x04, 0xa8, 0x17, 0xc8, 0x00, 0x82, 0x52, 0x08, 0x94, 0x35, 0x35, 0x35,
        0x35, 0x35, 0x35, 0x35, 0x35, 0x35, 0x35, 0x35, 0x35, 0x35, 0x35, 0x35,
        0x35, 0x35, 0x35, 0x35, 0x35, 0x88, 0x0d, 0xe0, 0xb6, 0xb3, 0xa7, 0x64,
        0x00, 0x00, 0x80, 0xc0,

        0x01, 0xa0, 0x28, 0xef, 0x61, 0x34, 0x0b, 0xd9, 0x39, 0xbc, 0x21, 0x95,
        0xfe, 0x53, 0x75, 0x67, 0x86, 0x60, 0x03, 0xe1, 0xa1, 0x5d, 0x3c, 0x71,
        0xff, 0x63, 0xe1, 0x59, 0x06, 0x20, 0xaa, 0x63, 0x62, 0x76, 0xa0, 0x67,
        0xcb, 0xe9, 0xd8, 0x99, 0x7f, 0x76, 0x1a, 0xec, 0xb7, 0x03, 0x30, 0x4b,
        0x38, 0x00, 0xcc, 0xf5, 0x55, 0xc9, 0xf3, 0xdc, 0x64, 0x21, 0x4b, 0x29,
        0x7f, 0xb1, 0x96, 0x6a, 0x3b, 0x6d, 0x83};
    auto const eip1559_rlp_transaction = monad::rlp::encode_transaction(t);
    EXPECT_EQ(eip1559_rlp_transaction, eip1559_transaction);

    byte_string_view encoded_transaction_view{eip1559_rlp_transaction};
    auto const decoded_transaction =
        decode_transaction(encoded_transaction_view);
    ASSERT_FALSE(decoded_transaction.has_error());
    EXPECT_EQ(encoded_transaction_view.size(), 0);

    EXPECT_EQ(decoded_transaction.value().nonce, t.nonce);
    EXPECT_EQ(decoded_transaction.value().max_fee_per_gas, t.max_fee_per_gas);
    EXPECT_EQ(decoded_transaction.value().gas_limit, t.gas_limit);
    EXPECT_EQ(decoded_transaction.value().value, t.value);
    EXPECT_EQ(*decoded_transaction.value().to, *t.to);
    EXPECT_EQ(decoded_transaction.value().to.value(), t.to.value());
    EXPECT_EQ(decoded_transaction.value().sc.r, t.sc.r);
    EXPECT_EQ(decoded_transaction.value().sc.s, t.sc.s);
    EXPECT_EQ(*decoded_transaction.value().sc.chain_id, *t.sc.chain_id);
    EXPECT_EQ(
        decoded_transaction.value().sc.chain_id.value(), t.sc.chain_id.value());
    EXPECT_EQ(decoded_transaction.value().type, t.type);
    EXPECT_EQ(
        decoded_transaction.value().max_priority_fee_per_gas,
        t.max_priority_fee_per_gas);

    EXPECT_EQ(
        decoded_transaction.value().access_list.size(), t.access_list.size());
    for (size_t i = 0u; i < t.access_list.size(); ++i) {
        EXPECT_EQ(
            decoded_transaction.value().access_list[i].a, t.access_list[i].a);
        EXPECT_EQ(
            decoded_transaction.value().access_list[i].keys.size(),
            t.access_list[i].keys.size());
        EXPECT_EQ(
            decoded_transaction.value().access_list[i].keys,
            t.access_list[i].keys);
    }
}

TEST(Rlp_Transaction, EncodeEip1559FalseParity)
{
    using namespace intx;
    using namespace evmc::literals;

    static constexpr auto price{20'000'000'000};
    static constexpr auto value{0xde0b6b3a7640000_u256};
    static constexpr auto tip{4'000'000'000};
    static constexpr auto to_addr{
        0x3535353535353535353535353535353535353535_address};
    static constexpr auto r{
        0x28ef61340bd939bc2195fe537567866003e1a15d3c71ff63e1590620aa636276_u256};
    static constexpr auto s{
        0x67cbe9d8997f761aecb703304b3800ccf555c9f3dc64214b297fb1966a3b6d83_u256};
    static monad::AccessList const a{};

    monad::Transaction const t{
        .sc = {.r = r, .s = s, .chain_id = 137, .y_parity = false}, // Polygon
        .nonce = 9,
        .max_fee_per_gas = price,
        .gas_limit = 21'000,
        .value = value,
        .to = to_addr,
        .type = monad::TransactionType::eip1559,
        .access_list = a,
        .max_priority_fee_per_gas = tip};
    monad::byte_string const eip1559_transaction{
        0x02, 0xf8, 0x74, 0x81, 0x89, 0x09, 0x84, 0xee, 0x6b, 0x28, 0x00, 0x85,
        0x04, 0xa8, 0x17, 0xc8, 0x00, 0x82, 0x52, 0x08, 0x94, 0x35, 0x35, 0x35,
        0x35, 0x35, 0x35, 0x35, 0x35, 0x35, 0x35, 0x35, 0x35, 0x35, 0x35, 0x35,
        0x35, 0x35, 0x35, 0x35, 0x35, 0x88, 0x0d, 0xe0, 0xb6, 0xb3, 0xa7, 0x64,
        0x00, 0x00, 0x80, 0xc0,

        0x80, 0xa0, 0x28, 0xef, 0x61, 0x34, 0x0b, 0xd9, 0x39, 0xbc, 0x21, 0x95,
        0xfe, 0x53, 0x75, 0x67, 0x86, 0x60, 0x03, 0xe1, 0xa1, 0x5d, 0x3c, 0x71,
        0xff, 0x63, 0xe1, 0x59, 0x06, 0x20, 0xaa, 0x63, 0x62, 0x76, 0xa0, 0x67,
        0xcb, 0xe9, 0xd8, 0x99, 0x7f, 0x76, 0x1a, 0xec, 0xb7, 0x03, 0x30, 0x4b,
        0x38, 0x00, 0xcc, 0xf5, 0x55, 0xc9, 0xf3, 0xdc, 0x64, 0x21, 0x4b, 0x29,
        0x7f, 0xb1, 0x96, 0x6a, 0x3b, 0x6d, 0x83};
    auto const eip1559_rlp_transaction = monad::rlp::encode_transaction(t);
    EXPECT_EQ(eip1559_rlp_transaction, eip1559_transaction);

    byte_string_view encoded_transaction_view{eip1559_rlp_transaction};
    auto const decoded_transaction =
        decode_transaction(encoded_transaction_view);
    ASSERT_FALSE(decoded_transaction.has_error());
    EXPECT_EQ(encoded_transaction_view.size(), 0);

    EXPECT_EQ(decoded_transaction.value().nonce, t.nonce);
    EXPECT_EQ(decoded_transaction.value().max_fee_per_gas, t.max_fee_per_gas);
    EXPECT_EQ(decoded_transaction.value().gas_limit, t.gas_limit);
    EXPECT_EQ(decoded_transaction.value().value, t.value);
    EXPECT_EQ(*decoded_transaction.value().to, *t.to);
    EXPECT_EQ(decoded_transaction.value().to.value(), t.to.value());
    EXPECT_EQ(decoded_transaction.value().sc.r, t.sc.r);
    EXPECT_EQ(decoded_transaction.value().sc.s, t.sc.s);
    EXPECT_EQ(*decoded_transaction.value().sc.chain_id, *t.sc.chain_id);
    EXPECT_EQ(
        decoded_transaction.value().sc.chain_id.value(), t.sc.chain_id.value());
    EXPECT_EQ(decoded_transaction.value().type, t.type);
    EXPECT_EQ(
        decoded_transaction.value().max_priority_fee_per_gas,
        t.max_priority_fee_per_gas);

    EXPECT_EQ(
        decoded_transaction.value().access_list.size(), t.access_list.size());
    for (size_t i = 0u; i < t.access_list.size(); ++i) {
        EXPECT_EQ(
            decoded_transaction.value().access_list[i].a, t.access_list[i].a);
        EXPECT_EQ(
            decoded_transaction.value().access_list[i].keys.size(),
            t.access_list[i].keys.size());
        EXPECT_EQ(
            decoded_transaction.value().access_list[i].keys,
            t.access_list[i].keys);
    }
}

TEST(Rlp_Transaction, IntTypeMismatchRegression)
{
    using intx::operator""_u256;
    using namespace evmc::literals;

    static constexpr auto to_addr{
        0x3535353535353535353535353535353535353535_address};
    static constexpr auto r{
        0x28ef61340bd939bc2195fe537567866003e1a15d3c71ff63e1590620aa636276_u256};
    static constexpr auto s{
        0x67cbe9d8997f761aecb703304b3800ccf555c9f3dc64214b297fb1966a3b6d83_u256};

    // Use a 72 bit chain ID!
    auto const bad_chain_id =
        std::make_optional<uint256_t>(0xFFFFFFFFFFFFFFFFFF_u256);
    Transaction const legacy_tx{
        .sc = {.r = r, .s = s, .chain_id = bad_chain_id},
        .nonce = 9,
        .max_fee_per_gas = 20'000'000'000,
        .gas_limit = 21'000,
        .value = 0xde0b6b3a7640000_u256,
        .to = to_addr};

    auto const legacy_rlp_tx = encode_transaction(legacy_tx);
    byte_string_view encoded_tx_view{legacy_rlp_tx};
    auto const decoded_tx = decode_transaction(encoded_tx_view);

    ASSERT_FALSE(decoded_tx.has_error());
    EXPECT_EQ(decoded_tx.value(), legacy_tx);
}
