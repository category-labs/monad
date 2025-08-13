// Copyright (C) 2025 Category Labs, Inc.
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

#include <category/execution/ethereum/core/address.hpp>
#include <category/execution/ethereum/precompiles.hpp>

#include <evmc/evmc.h>
#include <evmc/evmc.hpp>
#include <evmc/hex.hpp>

#include <gtest/gtest.h>

#include <cstddef>
#include <cstdint>
#include <iterator>
#include <string_view>
#include <vector>

using namespace monad;

using namespace evmc::literals;

// the following elliptic curve input data was directly copied from
// https://github.com/ethereum/go-ethereum/tree/master/core/vm/testdata/precompiles

static auto const ECRECOVER_UNRECOVERABLE_KEY_INPUT =
    evmc::from_hex(
        std::string_view{
            "a8b53bdf3306a35a7103ab5504a0c9b492295564b6202b1942a84ef3001072"
            "81000000000000000000000000000000000000000000000000000000000000"
            "001b3078356531653033663533636531386237373263636230303933666637"
            "31663366353366356337356237346463623331613835616138623838393262"
            "34653862112233445566778899101112131415161718192021222324252627"
            "2829303132"})
        .value();

static auto const ECRECOVER_VALID_KEY_INPUT =
    evmc::from_hex(
        std::string_view{
            "18c547e4f7b0f325ad1e56f57e26c745b09a3e503d86e00e5255ff7f715d3d1c00"
            "0000000000000000000000000000000000000000000000000000000000001c73b1"
            "693892219d736caba55bdb67216e485557ea6b6af75f37096c9aa6a5a75feeb940"
            "b1d03b21e36b0e47e79769f095fe2ab855bd91e3a38756b7d75a9c4549"})
        .value();

static auto const ECRECOVER_VALID_KEY_OUTPUT =
    evmc::from_hex(
        std::string_view{
            "000000000000000000000000a94f5374fce5edbc8e2a8697c15331677e6ebf0b"})
        .value();

// hash of empty string
static auto const SHA256_NULL_HASH =
    evmc::from_hex(
        std::string_view{
            "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"})
        .value();

// hash of the string "lol"
static auto const SHA256_LOL_HASH =
    evmc::from_hex(
        std::string_view{
            "07123e1f482356c415f684407a3b8723e10b2cbbc0b8fcd6282c49d37c9c1abc"})
        .value();

// hash of empty string padded to 32 bytes
static auto const RIPEMD160_NULL_HASH =
    evmc::from_hex(
        std::string_view{
            "0000000000000000000000009c1185a5c5e9fc54612808977ee8f548b2258d31"})
        .value();

// hash of the string "lol" padded to 32 bytes
static auto const RIPEMD160_LOL_HASH =
    evmc::from_hex(
        std::string_view{
            "00000000000000000000000014d61d472ae2e974453fb7a0ef239510f36bee24"})
        .value();

struct basic_test_case
{
    char const *name;
    evmc_message input;
    evmc_result expected_output;
};

static basic_test_case const ECRECOVER_TEST_CASES[] = {
    {.name = "ecrecover_unrecoverable_key_enough_gas",
     .input =
         {.gas = 6'000,
          .input_data = ECRECOVER_UNRECOVERABLE_KEY_INPUT.data(),
          .input_size = ECRECOVER_UNRECOVERABLE_KEY_INPUT.size(),
          .code_address = 0x01_address},
     .expected_output =
         {.status_code = evmc_status_code::EVMC_SUCCESS,
          .gas_left = 3'000,
          .output_size = 0}},
    {.name = "ecrecover_unrecoverable_key_insufficient_gas",
     .input =
         {.gas = 2'999,
          .input_data = ECRECOVER_UNRECOVERABLE_KEY_INPUT.data(),
          .input_size = ECRECOVER_UNRECOVERABLE_KEY_INPUT.size(),
          .code_address = 0x01_address},
     .expected_output = {.status_code = evmc_status_code::EVMC_OUT_OF_GAS}},
    {.name = "ecrecover_valid_key_enough_gas",
     .input =
         {.gas = 6'000,
          .input_data = ECRECOVER_VALID_KEY_INPUT.data(),
          .input_size = ECRECOVER_VALID_KEY_INPUT.size(),
          .code_address = 0x01_address},
     .expected_output =
         {.status_code = evmc_status_code::EVMC_SUCCESS,
          .gas_left = 3'000,
          .output_data = ECRECOVER_VALID_KEY_OUTPUT.data(),
          .output_size = ECRECOVER_VALID_KEY_OUTPUT.size()}},
    {.name = "ecrecover_valid_key_insufficient_gas",
     .input =
         {.gas = 2'999,
          .input_data = ECRECOVER_VALID_KEY_INPUT.data(),
          .input_size = ECRECOVER_VALID_KEY_INPUT.size(),
          .code_address = 0x01_address},
     .expected_output = {.status_code = evmc_status_code::EVMC_OUT_OF_GAS}}};

static basic_test_case const SHA256_TEST_CASES[] = {
    {.name = "sha256_empty_enough_gas",
     .input = {.gas = 100, .code_address = 0x02_address},
     .expected_output =
         {.status_code = evmc_status_code::EVMC_SUCCESS,
          .gas_left = 40,
          .output_data = SHA256_NULL_HASH.data(),
          .output_size = 32}},
    {.name = "sha256_empty_insufficient_gas",
     .input = {.gas = 59, .code_address = 0x02_address},
     .expected_output = {.status_code = evmc_status_code::EVMC_OUT_OF_GAS}},
    {.name = "sha256_message_enough_gas",
     .input =
         {.gas = 73,
          .input_data = reinterpret_cast<uint8_t const *>("lol"),
          .input_size = 3,
          .code_address = 0x02_address},
     .expected_output =
         {.status_code = evmc_status_code::EVMC_SUCCESS,
          .gas_left = 1,
          .output_data = SHA256_LOL_HASH.data(),
          .output_size = 32}},
    {.name = "sha256_message_insufficient_gas",
     .input =
         {.gas = 71,
          .input_data = reinterpret_cast<uint8_t const *>("lol"),
          .input_size = 3,
          .code_address = 0x02_address},
     .expected_output = {.status_code = evmc_status_code::EVMC_OUT_OF_GAS}}};

static basic_test_case const RIPEMD160_TEST_CASES[] = {
    {.name = "ripemd160_empty_enough_gas",
     .input = {.gas = 601, .code_address = 0x03_address},
     .expected_output =
         {.status_code = evmc_status_code::EVMC_SUCCESS,
          .gas_left = 1,
          .output_data = RIPEMD160_NULL_HASH.data(),
          .output_size = 32}},
    {.name = "ripemd160_empty_insufficient_gas",
     .input = {.gas = 599, .code_address = 0x03_address},
     .expected_output = {.status_code = evmc_status_code::EVMC_OUT_OF_GAS}},
    {.name = "ripemd160_message_enough_gas",
     .input =
         {.gas = 721,
          .input_data = reinterpret_cast<uint8_t const *>("lol"),
          .input_size = 3,
          .code_address = 0x03_address},
     .expected_output =
         {.status_code = evmc_status_code::EVMC_SUCCESS,
          .gas_left = 1,
          .output_data = RIPEMD160_LOL_HASH.data(),
          .output_size = 32}},
    {.name = "ripemd160_message_insufficient_gas",
     .input =
         {.gas = 619,
          .input_data = reinterpret_cast<uint8_t const *>("lol"),
          .input_size = 3,
          .code_address = 0x03_address},
     .expected_output = {.status_code = evmc_status_code::EVMC_OUT_OF_GAS}}};

static basic_test_case const IDENTITY_TEST_CASES[] = {
    {.name = "identity_empty_enough_gas",
     .input = {.gas = 16, .code_address = 0x04_address},
     .expected_output =
         {.status_code = evmc_status_code::EVMC_SUCCESS,
          .gas_left = 1,
          .output_size = 0}},
    {.name = "identity_empty_insufficient_gas",
     .input = {.gas = 14, .code_address = 0x04_address},
     .expected_output = {.status_code = evmc_status_code::EVMC_OUT_OF_GAS}},
    {.name = "identity_nonempty_enough_gas",
     .input =
         {.gas = 19,
          .input_data = reinterpret_cast<uint8_t const *>("dead"),
          .input_size = 4,
          .code_address = 0x04_address},
     .expected_output =
         {.status_code = evmc_status_code::EVMC_SUCCESS,
          .gas_left = 1,
          .output_data = reinterpret_cast<uint8_t const *>("dead"),
          .output_size = 4}},
    {.name = "identity_nonempty_insufficient_gas",
     .input =
         {.gas = 17,
          .input_data = reinterpret_cast<uint8_t const *>("dead"),
          .input_size = 4,
          .code_address = 0x04_address},
     .expected_output = {.status_code = evmc_status_code::EVMC_OUT_OF_GAS}}};

void do_basic_tests(
    char const *suite_name, basic_test_case const *basic_test_cases,
    size_t num_basic_test_cases)
{
    for (size_t i = 0; i < num_basic_test_cases; i++) {
        auto const &basic_test_case = basic_test_cases[i];

        evmc::Result const result =
            check_call_precompile<EVMC_BERLIN>(basic_test_case.input).value();

        EXPECT_EQ(
            result.status_code, basic_test_case.expected_output.status_code)
            << suite_name << " test case " << basic_test_case.name;

        if (result.status_code == evmc_status_code::EVMC_SUCCESS) {
            EXPECT_EQ(result.gas_left, basic_test_case.expected_output.gas_left)
                << suite_name << " test case " << basic_test_case.name
                << " gas check failed.";
        }
        else {
            EXPECT_EQ(result.gas_left, 0)
                << suite_name << " test case " << basic_test_case.name
                << " gas check failed. It should have cleared gas_left.";
        }

        ASSERT_EQ(
            result.output_size, basic_test_case.expected_output.output_size)
            << suite_name << " test case " << basic_test_case.name
            << " output buffer size check failed.";

        for (size_t idx = 0; idx < result.output_size; idx++) {
            EXPECT_EQ(
                basic_test_case.expected_output.output_data[idx],
                result.output_data[idx])
                << suite_name << " test case " << basic_test_case.name
                << " output buffer equality check failed.";
        }
    }
}

TEST(FrontierThroughHomestead, ecrecover)
{
    do_basic_tests(
        "ecrecover", ECRECOVER_TEST_CASES, std::size(ECRECOVER_TEST_CASES));
}

TEST(FrontierThroughHomestead, sha256)
{
    do_basic_tests("sha256", SHA256_TEST_CASES, std::size(SHA256_TEST_CASES));
}

TEST(FrontierThroughHomestead, ripemd160)
{
    do_basic_tests(
        "ripemd160", RIPEMD160_TEST_CASES, std::size(RIPEMD160_TEST_CASES));
}

TEST(FrontierThroughHomestead, identity)
{
    do_basic_tests(
        "identity", IDENTITY_TEST_CASES, std::size(IDENTITY_TEST_CASES));
}

TEST(SpuriousDragonThroughByzantium, ecrecover)
{
    do_basic_tests(
        "ecrecover", ECRECOVER_TEST_CASES, std::size(ECRECOVER_TEST_CASES));
}

TEST(SpuriousDragonThroughByzantium, sha256)
{
    do_basic_tests("sha256", SHA256_TEST_CASES, std::size(SHA256_TEST_CASES));
}

TEST(SpuriousDragonThroughByzantium, ripemd160_empty_enough_gas)
{
    do_basic_tests(
        "ripemd160", RIPEMD160_TEST_CASES, std::size(RIPEMD160_TEST_CASES));
}

TEST(SpuriousDragonThroughByzantium, identity_empty_enough_gas)
{
    do_basic_tests(
        "identity", IDENTITY_TEST_CASES, std::size(IDENTITY_TEST_CASES));
}

struct test_case
{
    char const *input;
    char const *expected;
    char const *name;
    int64_t gas;
};

// it was annoying to deduce the size of the array  :(
template <evmc_revision rev = EVMC_BERLIN>
void do_geth_tests(
    char const *suite_name, std::vector<test_case> const &test_cases,
    monad::Address const &code_address)
{
    for (auto const &test_case : test_cases) {
        auto const input_bytes =
            evmc::from_hex(std::string_view{test_case.input}).value();
        auto const expected_output_bytes =
            evmc::from_hex(std::string_view{test_case.expected}).value();

        auto test_with_gas_offset = [&](int64_t gas_offset) {
            evmc_message const input = {
                .gas = test_case.gas + gas_offset,
                .input_data = input_bytes.data(),
                .input_size = input_bytes.size(),
                .code_address = code_address};

            evmc::Result const result =
                check_call_precompile<rev>(input).value();

            if (result.status_code == evmc_status_code::EVMC_SUCCESS) {
                EXPECT_EQ(result.gas_left, gas_offset)
                    << suite_name << " test case " << test_case.name
                    << " gas check failed.";
            }
            else {
                EXPECT_EQ(result.gas_left, 0)
                    << suite_name << " test case " << test_case.name
                    << " gas check failed. It should have cleared gas_left.";
            }

            ASSERT_EQ(result.output_size, expected_output_bytes.size())
                << suite_name << " test case " << test_case.name
                << " output buffer size check failed.";

            for (size_t i = 0; i < result.output_size; i++) {
                EXPECT_EQ(expected_output_bytes[i], result.output_data[i])
                    << suite_name << " test case " << test_case.name
                    << " output buffer equality check failed.";
            }
        };

        test_with_gas_offset(0);
        test_with_gas_offset(100);
    }
}

// clang-format off
static const std::vector<test_case> MODEXP_BYZANTIUM_TEST_CASES =
{
    {
        .input = "00000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000002003fffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2efffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2f",
        .expected = "0000000000000000000000000000000000000000000000000000000000000001",
        .name = "eip_example1",
        .gas = 13056
    },
    {
        .input = "000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000020fffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2efffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2f",
        .expected = "0000000000000000000000000000000000000000000000000000000000000000",
        .name = "eip_example2",
        .gas = 13056
    },
    {
        .input = "000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000040e09ad9675465c53a109fac66a445c91b292d2bb2c5268addb30cd82f80fcb0033ff97c80a5fc6f39193ae969c6ede6710a6b7ac27078a06d90ef1c72e5c85fb502fc9e1f6beb81516545975218075ec2af118cd8798df6e08a147c60fd6095ac2bb02c2908cf4dd7c81f11c289e4bce98f3553768f392a80ce22bf5c4f4a248c6b",
        .expected = "60008f1614cc01dcfb6bfb09c625cf90b47d4468db81b5f8b7a39d42f332eab9b2da8f2d95311648a8f243f4bb13cfb3d8f7f2a3c014122ebb3ed41b02783adc",
        .name = "nagydani-1-square",
        .gas = 204
    },
    {
        .input = "000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000040e09ad9675465c53a109fac66a445c91b292d2bb2c5268addb30cd82f80fcb0033ff97c80a5fc6f39193ae969c6ede6710a6b7ac27078a06d90ef1c72e5c85fb503fc9e1f6beb81516545975218075ec2af118cd8798df6e08a147c60fd6095ac2bb02c2908cf4dd7c81f11c289e4bce98f3553768f392a80ce22bf5c4f4a248c6b",
        .expected = "4834a46ba565db27903b1c720c9d593e84e4cbd6ad2e64b31885d944f68cd801f92225a8961c952ddf2797fa4701b330c85c4b363798100b921a1a22a46a7fec",
        .name = "nagydani-1-qube",
        .gas = 204
    },
    {
        .input = "000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000030000000000000000000000000000000000000000000000000000000000000040e09ad9675465c53a109fac66a445c91b292d2bb2c5268addb30cd82f80fcb0033ff97c80a5fc6f39193ae969c6ede6710a6b7ac27078a06d90ef1c72e5c85fb5010001fc9e1f6beb81516545975218075ec2af118cd8798df6e08a147c60fd6095ac2bb02c2908cf4dd7c81f11c289e4bce98f3553768f392a80ce22bf5c4f4a248c6b",
        .expected = "c36d804180c35d4426b57b50c5bfcca5c01856d104564cd513b461d3c8b8409128a5573e416d0ebe38f5f736766d9dc27143e4da981dfa4d67f7dc474cbee6d2",
        .name = "nagydani-1-pow0x10001",
        .gas = 3276
    },
    {
        .input = "000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000080cad7d991a00047dd54d3399b6b0b937c718abddef7917c75b6681f40cc15e2be0003657d8d4c34167b2f0bbbca0ccaa407c2a6a07d50f1517a8f22979ce12a81dcaf707cc0cebfc0ce2ee84ee7f77c38b9281b9822a8d3de62784c089c9b18dcb9a2a5eecbede90ea788a862a9ddd9d609c2c52972d63e289e28f6a590ffbf5102e6d893b80aeed5e6e9ce9afa8a5d5675c93a32ac05554cb20e9951b2c140e3ef4e433068cf0fb73bc9f33af1853f64aa27a0028cbf570d7ac9048eae5dc7b28c87c31e5810f1e7fa2cda6adf9f1076dbc1ec1238560071e7efc4e9565c49be9e7656951985860a558a754594115830bcdb421f741408346dd5997bb01c287087",
        .expected = "981dd99c3b113fae3e3eaa9435c0dc96779a23c12a53d1084b4f67b0b053a27560f627b873e3f16ad78f28c94f14b6392def26e4d8896c5e3c984e50fa0b3aa44f1da78b913187c6128baa9340b1e9c9a0fd02cb78885e72576da4a8f7e5a113e173a7a2889fde9d407bd9f06eb05bc8fc7b4229377a32941a02bf4edcc06d70",
        .name = "nagydani-2-square",
        .gas = 665
    },
    {
        .input = "000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000080cad7d991a00047dd54d3399b6b0b937c718abddef7917c75b6681f40cc15e2be0003657d8d4c34167b2f0bbbca0ccaa407c2a6a07d50f1517a8f22979ce12a81dcaf707cc0cebfc0ce2ee84ee7f77c38b9281b9822a8d3de62784c089c9b18dcb9a2a5eecbede90ea788a862a9ddd9d609c2c52972d63e289e28f6a590ffbf5103e6d893b80aeed5e6e9ce9afa8a5d5675c93a32ac05554cb20e9951b2c140e3ef4e433068cf0fb73bc9f33af1853f64aa27a0028cbf570d7ac9048eae5dc7b28c87c31e5810f1e7fa2cda6adf9f1076dbc1ec1238560071e7efc4e9565c49be9e7656951985860a558a754594115830bcdb421f741408346dd5997bb01c287087",
        .expected = "d89ceb68c32da4f6364978d62aaa40d7b09b59ec61eb3c0159c87ec3a91037f7dc6967594e530a69d049b64adfa39c8fa208ea970cfe4b7bcd359d345744405afe1cbf761647e32b3184c7fbe87cee8c6c7ff3b378faba6c68b83b6889cb40f1603ee68c56b4c03d48c595c826c041112dc941878f8c5be828154afd4a16311f",
        .name = "nagydani-2-qube",
        .gas = 665
    },
    {
        .input = "000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000030000000000000000000000000000000000000000000000000000000000000080cad7d991a00047dd54d3399b6b0b937c718abddef7917c75b6681f40cc15e2be0003657d8d4c34167b2f0bbbca0ccaa407c2a6a07d50f1517a8f22979ce12a81dcaf707cc0cebfc0ce2ee84ee7f77c38b9281b9822a8d3de62784c089c9b18dcb9a2a5eecbede90ea788a862a9ddd9d609c2c52972d63e289e28f6a590ffbf51010001e6d893b80aeed5e6e9ce9afa8a5d5675c93a32ac05554cb20e9951b2c140e3ef4e433068cf0fb73bc9f33af1853f64aa27a0028cbf570d7ac9048eae5dc7b28c87c31e5810f1e7fa2cda6adf9f1076dbc1ec1238560071e7efc4e9565c49be9e7656951985860a558a754594115830bcdb421f741408346dd5997bb01c287087",
        .expected = "ad85e8ef13fd1dd46eae44af8b91ad1ccae5b7a1c92944f92a19f21b0b658139e0cabe9c1f679507c2de354bf2c91ebd965d1e633978a830d517d2f6f8dd5fd58065d58559de7e2334a878f8ec6992d9b9e77430d4764e863d77c0f87beede8f2f7f2ab2e7222f85cc9d98b8467f4bb72e87ef2882423ebdb6daf02dddac6db2",
        .name = "nagydani-2-pow0x10001",
        .gas = 10649
    },
    {
        .input = "000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000100c9130579f243e12451760976261416413742bd7c91d39ae087f46794062b8c239f2a74abf3918605a0e046a7890e049475ba7fbb78f5de6490bd22a710cc04d30088179a919d86c2da62cf37f59d8f258d2310d94c24891be2d7eeafaa32a8cb4b0cfe5f475ed778f45907dc8916a73f03635f233f7a77a00a3ec9ca6761a5bbd558a2318ecd0caa1c5016691523e7e1fa267dd35e70c66e84380bdcf7c0582f540174e572c41f81e93da0b757dff0b0fe23eb03aa19af0bdec3afb474216febaacb8d0381e631802683182b0fe72c28392539850650b70509f54980241dc175191a35d967288b532a7a8223ce2440d010615f70df269501944d4ec16fe4a3cb02d7a85909174757835187cb52e71934e6c07ef43b4c46fc30bbcd0bc72913068267c54a4aabebb493922492820babdeb7dc9b1558fcf7bd82c37c82d3147e455b623ab0efa752fe0b3a67ca6e4d126639e645a0bf417568adbb2a6a4eef62fa1fa29b2a5a43bebea1f82193a7dd98eb483d09bb595af1fa9c97c7f41f5649d976aee3e5e59e2329b43b13bea228d4a93f16ba139ccb511de521ffe747aa2eca664f7c9e33da59075cc335afcd2bf3ae09765f01ab5a7c3e3938ec168b74724b5074247d200d9970382f683d6059b94dbc336603d1dfee714e4b447ac2fa1d99ecb4961da2854e03795ed758220312d101e1e3d87d5313a6d052aebde75110363d",
        .expected = "affc7507ea6d84751ec6b3f0d7b99dbcc263f33330e450d1b3ff0bc3d0874320bf4edd57debd587306988157958cb3cfd369cc0c9c198706f635c9e0f15d047df5cb44d03e2727f26b083c4ad8485080e1293f171c1ed52aef5993a5815c35108e848c951cf1e334490b4a539a139e57b68f44fee583306f5b85ffa57206b3ee5660458858534e5386b9584af3c7f67806e84c189d695e5eb96e1272d06ec2df5dc5fabc6e94b793718c60c36be0a4d031fc84cd658aa72294b2e16fc240aef70cb9e591248e38bd49c5a554d1afa01f38dab72733092f7555334bbef6c8c430119840492380aa95fa025dcf699f0a39669d812b0c6946b6091e6e235337b6f8",
        .name = "nagydani-3-square",
        .gas = 1894
    },
    {
        .input = "000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000100c9130579f243e12451760976261416413742bd7c91d39ae087f46794062b8c239f2a74abf3918605a0e046a7890e049475ba7fbb78f5de6490bd22a710cc04d30088179a919d86c2da62cf37f59d8f258d2310d94c24891be2d7eeafaa32a8cb4b0cfe5f475ed778f45907dc8916a73f03635f233f7a77a00a3ec9ca6761a5bbd558a2318ecd0caa1c5016691523e7e1fa267dd35e70c66e84380bdcf7c0582f540174e572c41f81e93da0b757dff0b0fe23eb03aa19af0bdec3afb474216febaacb8d0381e631802683182b0fe72c28392539850650b70509f54980241dc175191a35d967288b532a7a8223ce2440d010615f70df269501944d4ec16fe4a3cb03d7a85909174757835187cb52e71934e6c07ef43b4c46fc30bbcd0bc72913068267c54a4aabebb493922492820babdeb7dc9b1558fcf7bd82c37c82d3147e455b623ab0efa752fe0b3a67ca6e4d126639e645a0bf417568adbb2a6a4eef62fa1fa29b2a5a43bebea1f82193a7dd98eb483d09bb595af1fa9c97c7f41f5649d976aee3e5e59e2329b43b13bea228d4a93f16ba139ccb511de521ffe747aa2eca664f7c9e33da59075cc335afcd2bf3ae09765f01ab5a7c3e3938ec168b74724b5074247d200d9970382f683d6059b94dbc336603d1dfee714e4b447ac2fa1d99ecb4961da2854e03795ed758220312d101e1e3d87d5313a6d052aebde75110363d",
        .expected = "1b280ecd6a6bf906b806d527c2a831e23b238f89da48449003a88ac3ac7150d6a5e9e6b3be4054c7da11dd1e470ec29a606f5115801b5bf53bc1900271d7c3ff3cd5ed790d1c219a9800437a689f2388ba1a11d68f6a8e5b74e9a3b1fac6ee85fc6afbac599f93c391f5dc82a759e3c6c0ab45ce3f5d25d9b0c1bf94cf701ea6466fc9a478dacc5754e593172b5111eeba88557048bceae401337cd4c1182ad9f700852bc8c99933a193f0b94cf1aedbefc48be3bc93ef5cb276d7c2d5462ac8bb0c8fe8923a1db2afe1c6b90d59c534994a6a633f0ead1d638fdc293486bb634ff2c8ec9e7297c04241a61c37e3ae95b11d53343d4ba2b4cc33d2cfa7eb705e",
        .name = "nagydani-3-qube",
        .gas = 1894
    },
    {
        .input = "000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000030000000000000000000000000000000000000000000000000000000000000100c9130579f243e12451760976261416413742bd7c91d39ae087f46794062b8c239f2a74abf3918605a0e046a7890e049475ba7fbb78f5de6490bd22a710cc04d30088179a919d86c2da62cf37f59d8f258d2310d94c24891be2d7eeafaa32a8cb4b0cfe5f475ed778f45907dc8916a73f03635f233f7a77a00a3ec9ca6761a5bbd558a2318ecd0caa1c5016691523e7e1fa267dd35e70c66e84380bdcf7c0582f540174e572c41f81e93da0b757dff0b0fe23eb03aa19af0bdec3afb474216febaacb8d0381e631802683182b0fe72c28392539850650b70509f54980241dc175191a35d967288b532a7a8223ce2440d010615f70df269501944d4ec16fe4a3cb010001d7a85909174757835187cb52e71934e6c07ef43b4c46fc30bbcd0bc72913068267c54a4aabebb493922492820babdeb7dc9b1558fcf7bd82c37c82d3147e455b623ab0efa752fe0b3a67ca6e4d126639e645a0bf417568adbb2a6a4eef62fa1fa29b2a5a43bebea1f82193a7dd98eb483d09bb595af1fa9c97c7f41f5649d976aee3e5e59e2329b43b13bea228d4a93f16ba139ccb511de521ffe747aa2eca664f7c9e33da59075cc335afcd2bf3ae09765f01ab5a7c3e3938ec168b74724b5074247d200d9970382f683d6059b94dbc336603d1dfee714e4b447ac2fa1d99ecb4961da2854e03795ed758220312d101e1e3d87d5313a6d052aebde75110363d",
        .expected = "37843d7c67920b5f177372fa56e2a09117df585f81df8b300fba245b1175f488c99476019857198ed459ed8d9799c377330e49f4180c4bf8e8f66240c64f65ede93d601f957b95b83efdee1e1bfde74169ff77002eaf078c71815a9220c80b2e3b3ff22c2f358111d816ebf83c2999026b6de50bfc711ff68705d2f40b753424aefc9f70f08d908b5a20276ad613b4ab4309a3ea72f0c17ea9df6b3367d44fb3acab11c333909e02e81ea2ed404a712d3ea96bba87461720e2d98723e7acd0520ac1a5212dbedcd8dc0c1abf61d4719e319ff4758a774790b8d463cdfe131d1b2dcfee52d002694e98e720cb6ae7ccea353bc503269ba35f0f63bf8d7b672a76",
        .name = "nagydani-3-pow0x10001",
        .gas = 30310
    },
    {
        .input = "000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000200db34d0e438249c0ed685c949cc28776a05094e1c48691dc3f2dca5fc3356d2a0663bd376e4712839917eb9a19c670407e2c377a2de385a3ff3b52104f7f1f4e0c7bf7717fb913896693dc5edbb65b760ef1b00e42e9d8f9af17352385e1cd742c9b006c0f669995cb0bb21d28c0aced2892267637b6470d8cee0ab27fc5d42658f6e88240c31d6774aa60a7ebd25cd48b56d0da11209f1928e61005c6eb709f3e8e0aaf8d9b10f7d7e296d772264dc76897ccdddadc91efa91c1903b7232a9e4c3b941917b99a3bc0c26497dedc897c25750af60237aa67934a26a2bc491db3dcc677491944bc1f51d3e5d76b8d846a62db03dedd61ff508f91a56d71028125035c3a44cbb041497c83bf3e4ae2a9613a401cc721c547a2afa3b16a2969933d3626ed6d8a7428648f74122fd3f2a02a20758f7f693892c8fd798b39abac01d18506c45e71432639e9f9505719ee822f62ccbf47f6850f096ff77b5afaf4be7d772025791717dbe5abf9b3f40cff7d7aab6f67e38f62faf510747276e20a42127e7500c444f9ed92baf65ade9e836845e39c4316d9dce5f8e2c8083e2c0acbb95296e05e51aab13b6b8f53f06c9c4276e12b0671133218cc3ea907da3bd9a367096d9202128d14846cc2e20d56fc8473ecb07cecbfb8086919f3971926e7045b853d85a69d026195c70f9f7a823536e2a8f4b3e12e94d9b53a934353451094b8102df3143a0057457d75e8c708b6337a6f5a4fd1a06727acf9fb93e2993c62f3378b37d56c85e7b1e00f0145ebf8e4095bd723166293c60b6ac1252291ef65823c9e040ddad14969b3b340a4ef714db093a587c37766d68b8d6b5016e741587e7e6bf7e763b44f0247e64bae30f994d248bfd20541a333e5b225ef6a61199e301738b1e688f70ec1d7fb892c183c95dc543c3e12adf8a5e8b9ca9d04f9445cced3ab256f29e998e69efaa633a7b60e1db5a867924ccab0a171d9d6e1098dfa15acde9553de599eaa56490c8f411e4985111f3d40bddfc5e301edb01547b01a886550a61158f7e2033c59707789bf7c854181d0c2e2a42a93cf09209747d7082e147eb8544de25c3eb14f2e35559ea0c0f5877f2f3fc92132c0ae9da4e45b2f6c866a224ea6d1f28c05320e287750fbc647368d41116e528014cc1852e5531d53e4af938374daba6cee4baa821ed07117253bb3601ddd00d59a3d7fb2ef1f5a2fbba7c429f0cf9a5b3462410fd833a69118f8be9c559b1000cc608fd877fb43f8e65c2d1302622b944462579056874b387208d90623fcdaf93920ca7a9e4ba64ea208758222ad868501cc2c345e2d3a5ea2a17e5069248138c8a79c0251185d29ee73e5afab5354769142d2bf0cb6712727aa6bf84a6245fcdae66e4938d84d1b9dd09a884818622080ff5f98942fb20acd7e0c916c2d5ea7ce6f7e173315384518f",
        .expected = "8a5aea5f50dcc03dc7a7a272b5aeebc040554dbc1ffe36753c4fc75f7ed5f6c2cc0de3a922bf96c78bf0643a73025ad21f45a4a5cadd717612c511ab2bff1190fe5f1ae05ba9f8fe3624de1de2a817da6072ddcdb933b50216811dbe6a9ca79d3a3c6b3a476b079fd0d05f04fb154e2dd3e5cb83b148a006f2bcbf0042efb2ae7b916ea81b27aac25c3bf9a8b6d35440062ad8eae34a83f3ffa2cc7b40346b62174a4422584f72f95316f6b2bee9ff232ba9739301c97c99a9ded26c45d72676eb856ad6ecc81d36a6de36d7f9dafafee11baa43a4b0d5e4ecffa7b9b7dcefd58c397dd373e6db4acd2b2c02717712e6289bed7c813b670c4a0c6735aa7f3b0f1ce556eae9fcc94b501b2c8781ba50a8c6220e8246371c3c7359fe4ef9da786ca7d98256754ca4e496be0a9174bedbecb384bdf470779186d6a833f068d2838a88d90ef3ad48ff963b67c39cc5a3ee123baf7bf3125f64e77af7f30e105d72c4b9b5b237ed251e4c122c6d8c1405e736299c3afd6db16a28c6a9cfa68241e53de4cd388271fe534a6a9b0dbea6171d170db1b89858468885d08fecbd54c8e471c3e25d48e97ba450b96d0d87e00ac732aaa0d3ce4309c1064bd8a4c0808a97e0143e43a24cfa847635125cd41c13e0574487963e9d725c01375db99c31da67b4cf65eff555f0c0ac416c727ff8d438ad7c42030551d68c2e7adda0abb1ca7c10",
        .name = "nagydani-4-square",
        .gas = 5580
    },
    {
        .input = "000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000200db34d0e438249c0ed685c949cc28776a05094e1c48691dc3f2dca5fc3356d2a0663bd376e4712839917eb9a19c670407e2c377a2de385a3ff3b52104f7f1f4e0c7bf7717fb913896693dc5edbb65b760ef1b00e42e9d8f9af17352385e1cd742c9b006c0f669995cb0bb21d28c0aced2892267637b6470d8cee0ab27fc5d42658f6e88240c31d6774aa60a7ebd25cd48b56d0da11209f1928e61005c6eb709f3e8e0aaf8d9b10f7d7e296d772264dc76897ccdddadc91efa91c1903b7232a9e4c3b941917b99a3bc0c26497dedc897c25750af60237aa67934a26a2bc491db3dcc677491944bc1f51d3e5d76b8d846a62db03dedd61ff508f91a56d71028125035c3a44cbb041497c83bf3e4ae2a9613a401cc721c547a2afa3b16a2969933d3626ed6d8a7428648f74122fd3f2a02a20758f7f693892c8fd798b39abac01d18506c45e71432639e9f9505719ee822f62ccbf47f6850f096ff77b5afaf4be7d772025791717dbe5abf9b3f40cff7d7aab6f67e38f62faf510747276e20a42127e7500c444f9ed92baf65ade9e836845e39c4316d9dce5f8e2c8083e2c0acbb95296e05e51aab13b6b8f53f06c9c4276e12b0671133218cc3ea907da3bd9a367096d9202128d14846cc2e20d56fc8473ecb07cecbfb8086919f3971926e7045b853d85a69d026195c70f9f7a823536e2a8f4b3e12e94d9b53a934353451094b8103df3143a0057457d75e8c708b6337a6f5a4fd1a06727acf9fb93e2993c62f3378b37d56c85e7b1e00f0145ebf8e4095bd723166293c60b6ac1252291ef65823c9e040ddad14969b3b340a4ef714db093a587c37766d68b8d6b5016e741587e7e6bf7e763b44f0247e64bae30f994d248bfd20541a333e5b225ef6a61199e301738b1e688f70ec1d7fb892c183c95dc543c3e12adf8a5e8b9ca9d04f9445cced3ab256f29e998e69efaa633a7b60e1db5a867924ccab0a171d9d6e1098dfa15acde9553de599eaa56490c8f411e4985111f3d40bddfc5e301edb01547b01a886550a61158f7e2033c59707789bf7c854181d0c2e2a42a93cf09209747d7082e147eb8544de25c3eb14f2e35559ea0c0f5877f2f3fc92132c0ae9da4e45b2f6c866a224ea6d1f28c05320e287750fbc647368d41116e528014cc1852e5531d53e4af938374daba6cee4baa821ed07117253bb3601ddd00d59a3d7fb2ef1f5a2fbba7c429f0cf9a5b3462410fd833a69118f8be9c559b1000cc608fd877fb43f8e65c2d1302622b944462579056874b387208d90623fcdaf93920ca7a9e4ba64ea208758222ad868501cc2c345e2d3a5ea2a17e5069248138c8a79c0251185d29ee73e5afab5354769142d2bf0cb6712727aa6bf84a6245fcdae66e4938d84d1b9dd09a884818622080ff5f98942fb20acd7e0c916c2d5ea7ce6f7e173315384518f",
        .expected = "5a2664252aba2d6e19d9600da582cdd1f09d7a890ac48e6b8da15ae7c6ff1856fc67a841ac2314d283ffa3ca81a0ecf7c27d89ef91a5a893297928f5da0245c99645676b481b7e20a566ee6a4f2481942bee191deec5544600bb2441fd0fb19e2ee7d801ad8911c6b7750affec367a4b29a22942c0f5f4744a4e77a8b654da2a82571037099e9c6d930794efe5cdca73c7b6c0844e386bdca8ea01b3d7807146bb81365e2cdc6475f8c23e0ff84463126189dc9789f72bbce2e3d2d114d728a272f1345122de23df54c922ec7a16e5c2a8f84da8871482bd258c20a7c09bbcd64c7a96a51029bbfe848736a6ba7bf9d931a9b7de0bcaf3635034d4958b20ae9ab3a95a147b0421dd5f7ebff46c971010ebfc4adbbe0ad94d5498c853e7142c450d8c71de4b2f84edbf8acd2e16d00c8115b150b1c30e553dbb82635e781379fe2a56360420ff7e9f70cc64c00aba7e26ed13c7c19622865ae07248daced36416080f35f8cc157a857ed70ea4f347f17d1bee80fa038abd6e39b1ba06b97264388b21364f7c56e192d4b62d9b161405f32ab1e2594e86243e56fcf2cb30d21adef15b9940f91af681da24328c883d892670c6aa47940867a81830a82b82716895db810df1b834640abefb7db2092dd92912cb9a735175bc447be40a503cf22dfe565b4ed7a3293ca0dfd63a507430b323ee248ec82e843b673c97ad730728cebc",
        .name = "nagydani-4-qube",
        .gas = 5580
    },
    {
        .input = "000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000030000000000000000000000000000000000000000000000000000000000000200db34d0e438249c0ed685c949cc28776a05094e1c48691dc3f2dca5fc3356d2a0663bd376e4712839917eb9a19c670407e2c377a2de385a3ff3b52104f7f1f4e0c7bf7717fb913896693dc5edbb65b760ef1b00e42e9d8f9af17352385e1cd742c9b006c0f669995cb0bb21d28c0aced2892267637b6470d8cee0ab27fc5d42658f6e88240c31d6774aa60a7ebd25cd48b56d0da11209f1928e61005c6eb709f3e8e0aaf8d9b10f7d7e296d772264dc76897ccdddadc91efa91c1903b7232a9e4c3b941917b99a3bc0c26497dedc897c25750af60237aa67934a26a2bc491db3dcc677491944bc1f51d3e5d76b8d846a62db03dedd61ff508f91a56d71028125035c3a44cbb041497c83bf3e4ae2a9613a401cc721c547a2afa3b16a2969933d3626ed6d8a7428648f74122fd3f2a02a20758f7f693892c8fd798b39abac01d18506c45e71432639e9f9505719ee822f62ccbf47f6850f096ff77b5afaf4be7d772025791717dbe5abf9b3f40cff7d7aab6f67e38f62faf510747276e20a42127e7500c444f9ed92baf65ade9e836845e39c4316d9dce5f8e2c8083e2c0acbb95296e05e51aab13b6b8f53f06c9c4276e12b0671133218cc3ea907da3bd9a367096d9202128d14846cc2e20d56fc8473ecb07cecbfb8086919f3971926e7045b853d85a69d026195c70f9f7a823536e2a8f4b3e12e94d9b53a934353451094b81010001df3143a0057457d75e8c708b6337a6f5a4fd1a06727acf9fb93e2993c62f3378b37d56c85e7b1e00f0145ebf8e4095bd723166293c60b6ac1252291ef65823c9e040ddad14969b3b340a4ef714db093a587c37766d68b8d6b5016e741587e7e6bf7e763b44f0247e64bae30f994d248bfd20541a333e5b225ef6a61199e301738b1e688f70ec1d7fb892c183c95dc543c3e12adf8a5e8b9ca9d04f9445cced3ab256f29e998e69efaa633a7b60e1db5a867924ccab0a171d9d6e1098dfa15acde9553de599eaa56490c8f411e4985111f3d40bddfc5e301edb01547b01a886550a61158f7e2033c59707789bf7c854181d0c2e2a42a93cf09209747d7082e147eb8544de25c3eb14f2e35559ea0c0f5877f2f3fc92132c0ae9da4e45b2f6c866a224ea6d1f28c05320e287750fbc647368d41116e528014cc1852e5531d53e4af938374daba6cee4baa821ed07117253bb3601ddd00d59a3d7fb2ef1f5a2fbba7c429f0cf9a5b3462410fd833a69118f8be9c559b1000cc608fd877fb43f8e65c2d1302622b944462579056874b387208d90623fcdaf93920ca7a9e4ba64ea208758222ad868501cc2c345e2d3a5ea2a17e5069248138c8a79c0251185d29ee73e5afab5354769142d2bf0cb6712727aa6bf84a6245fcdae66e4938d84d1b9dd09a884818622080ff5f98942fb20acd7e0c916c2d5ea7ce6f7e173315384518f",
        .expected = "bed8b970c4a34849fc6926b08e40e20b21c15ed68d18f228904878d4370b56322d0da5789da0318768a374758e6375bfe4641fca5285ec7171828922160f48f5ca7efbfee4d5148612c38ad683ae4e3c3a053d2b7c098cf2b34f2cb19146eadd53c86b2d7ccf3d83b2c370bfb840913ee3879b1057a6b4e07e110b6bcd5e958bc71a14798c91d518cc70abee264b0d25a4110962a764b364ac0b0dd1ee8abc8426d775ec0f22b7e47b32576afaf1b5a48f64573ed1c5c29f50ab412188d9685307323d990802b81dacc06c6e05a1e901830ba9fcc67688dc29c5e27bde0a6e845ca925f5454b6fb3747edfaa2a5820838fb759eadf57f7cb5cec57fc213ddd8a4298fa079c3c0f472b07fb15aa6a7f0a3780bd296ff6a62e58ef443870b02260bd4fd2bbc98255674b8e1f1f9f8d33c7170b0ebbea4523b695911abbf26e41885344823bd0587115fdd83b721a4e8457a31c9a84b3d3520a07e0e35df7f48e5a9d534d0ec7feef1ff74de6a11e7f93eab95175b6ce22c68d78a642ad642837897ec11349205d8593ac19300207572c38d29ca5dfa03bc14cdbc32153c80e5cc3e739403d34c75915e49beb43094cc6dcafb3665b305ddec9286934ae66ec6b777ca528728c851318eb0f207b39f1caaf96db6eeead6b55ed08f451939314577d42bcc9f97c0b52d0234f88fd07e4c1d7780fdebc025cfffcb572cb27a8c33963",
        .name = "nagydani-4-pow0x10001",
        .gas = 89292
    },
    {
        .input = "000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000400c5a1611f8be90071a43db23cc2fe01871cc4c0e8ab5743f6378e4fef77f7f6db0095c0727e20225beb665645403453e325ad5f9aeb9ba99bf3c148f63f9c07cf4fe8847ad5242d6b7d4499f93bd47056ddab8f7dee878fc2314f344dbee2a7c41a5d3db91eff372c730c2fdd3a141a4b61999e36d549b9870cf2f4e632c4d5df5f024f81c028000073a0ed8847cfb0593d36a47142f578f05ccbe28c0c06aeb1b1da027794c48db880278f79ba78ae64eedfea3c07d10e0562668d839749dc95f40467d15cf65b9cfc52c7c4bcef1cda3596dd52631aac942f146c7cebd46065131699ce8385b0db1874336747ee020a5698a3d1a1082665721e769567f579830f9d259cec1a836845109c21cf6b25da572512bf3c42fd4b96e43895589042ab60dd41f497db96aec102087fe784165bb45f942859268fd2ff6c012d9d00c02ba83eace047cc5f7b2c392c2955c58a49f0338d6fc58749c9db2155522ac17914ec216ad87f12e0ee95574613942fa615898c4d9e8a3be68cd6afa4e7a003dedbdf8edfee31162b174f965b20ae752ad89c967b3068b6f722c16b354456ba8e280f987c08e0a52d40a2e8f3a59b94d590aeef01879eb7a90b3ee7d772c839c85519cbeaddc0c193ec4874a463b53fcaea3271d80ebfb39b33489365fc039ae549a17a9ff898eea2f4cb27b8dbee4c17b998438575b2b8d107e4a0d66ba7fca85b41a58a8d51f191a35c856dfbe8aef2b00048a694bbccff832d23c8ca7a7ff0b6c0b3011d00b97c86c0628444d267c951d9e4fb8f83e154b8f74fb51aa16535e498235c5597dac9606ed0be3173a3836baa4e7d756ffe1e2879b415d3846bccd538c05b847785699aefde3e305decb600cd8fb0e7d8de5efc26971a6ad4e6d7a2d91474f1023a0ac4b78dc937da0ce607a45974d2cac1c33a2631ff7fe6144a3b2e5cf98b531a9627dea92c1dc82204d09db0439b6a11dd64b484e1263aa45fd9539b6020b55e3baece3986a8bffc1003406348f5c61265099ed43a766ee4f93f5f9c5abbc32a0fd3ac2b35b87f9ec26037d88275bd7dd0a54474995ee34ed3727f3f97c48db544b1980193a4b76a8a3ddab3591ce527f16d91882e67f0103b5cda53f7da54d489fc4ac08b6ab358a5a04aa9daa16219d50bd672a7cb804ed769d218807544e5993f1c27427104b349906a0b654df0bf69328afd3013fbe430155339c39f236df5557bf92f1ded7ff609a8502f49064ec3d1dbfb6c15d3a4c11a4f8acd12278cbf68acd5709463d12e3338a6eddb8c112f199645e23154a8e60879d2a654e3ed9296aa28f134168619691cd2c6b9e2eba4438381676173fc63c2588a3c5910dc149cf3760f0aa9fa9c3f5faa9162b0bf1aac9dd32b706a60ef53cbdb394b6b40222b5bc80eea82ba8958386672564cae3794f977871ab62337cf02e30049201ec12937e7ce79d0f55d9c810e20acf52212aca1d3888949e0e4830aad88d804161230eb89d4d329cc83570fe257217d2119134048dd2ed167646975fc7d77136919a049ea74cf08ddd2b896890bb24a0ba18094a22baa351bf29ad96c66bbb1a598f2ca391749620e62d61c3561a7d3653ccc8892c7b99baaf76bf836e2991cb06d6bc0514568ff0d1ec8bb4b3d6984f5eaefb17d3ea2893722375d3ddb8e389a8eef7d7d198f8e687d6a513983df906099f9a2d23f4f9dec6f8ef2f11fc0a21fac45353b94e00486f5e17d386af42502d09db33cf0cf28310e049c07e88682aeeb00cb833c5174266e62407a57583f1f88b304b7c6e0c84bbe1c0fd423072d37a5bd0aacf764229e5c7cd02473460ba3645cd8e8ae144065bf02d0dd238593d8e230354f67e0b2f23012c23274f80e3ee31e35e2606a4a3f31d94ab755e6d163cff52cbb36b6d0cc67ffc512aeed1dce4d7a0d70ce82f2baba12e8d514dc92a056f994adfb17b5b9712bd5186f27a2fda1f7039c5df2c8587fdc62f5627580c13234b55be4df3056050e2d1ef3218f0dd66cb05265fe1acfb0989d8213f2c19d1735a7cf3fa65d88dad5af52dc2bba22b7abf46c3bc77b5091baab9e8f0ddc4d5e581037de91a9f8dcbc69309be29cc815cf19a20a7585b8b3073edf51fc9baeb3e509b97fa4ecfd621e0fd57bd61cac1b895c03248ff12bdbc57509250df3517e8a3fe1d776836b34ab352b973d932ef708b14f7418f9eceb1d87667e61e3e758649cb083f01b133d37ab2f5afa96d6c84bcacf4efc3851ad308c1e7d9113624fce29fab460ab9d2a48d92cdb281103a5250ad44cb2ff6e67ac670c02fdafb3e0f1353953d6d7d5646ca1568dea55275a050ec501b7c6250444f7219f1ba7521ba3b93d089727ca5f3bbe0d6c1300b423377004954c5628fdb65770b18ced5c9b23a4a5a6d6ef25fe01b4ce278de0bcc4ed86e28a0a68818ffa40970128cf2c38740e80037984428c1bd5113f40ff47512ee6f4e4d8f9b8e8e1b3040d2928d003bd1c1329dc885302fbce9fa81c23b4dc49c7c82d29b52957847898676c89aa5d32b5b0e1c0d5a2b79a19d67562f407f19425687971a957375879d90c5f57c857136c17106c9ab1b99d80e69c8c954ed386493368884b55c939b8d64d26f643e800c56f90c01079d7c534e3b2b7ae352cefd3016da55f6a85eb803b85e2304915fd2001f77c74e28746293c46e4f5f0fd49cf988aafd0026b8e7a3bab2da5cdce1ea26c2e29ec03f4807fac432662b2d6c060be1c7be0e5489de69d0a6e03a4b9117f9244b34a0f1ecba89884f781c6320412413a00c4980287409a2a78c2cd7e65cecebbe4ec1c28cac4dd95f6998e78fc6f1392384331c9436aa10e10e2bf8ad2c4eafbcf276aa7bae64b74428911b3269c749338b0fc5075ad",
        .expected = "d61fe4e3f32ac260915b5b03b78a86d11bfc41d973fce5b0cc59035cf8289a8a2e3878ea15fa46565b0d806e2f85b53873ea20ed653869b688adf83f3ef444535bf91598ff7e80f334fb782539b92f39f55310cc4b35349ab7b278346eda9bc37c0d8acd3557fae38197f412f8d9e57ce6a76b7205c23564cab06e5615be7c6f05c3d05ec690cba91da5e89d55b152ff8dd2157dc5458190025cf94b1ad98f7cbe64e9482faba95e6b33844afc640892872b44a9932096508f4a782a4805323808f23e54b6ff9b841dbfa87db3505ae4f687972c18ea0f0d0af89d36c1c2a5b14560c153c3fee406f5cf15cfd1c0bb45d767426d465f2f14c158495069d0c5955a00150707862ecaae30624ebacdd8ac33e4e6aab3ff90b6ba445a84689386b9e945d01823a65874444316e83767290fcff630d2477f49d5d8ffdd200e08ee1274270f86ed14c687895f6caf5ce528bd970c20d2408a9ba66216324c6a011ac4999098362dbd98a038129a2d40c8da6ab88318aa3046cb660327cc44236d9e5d2163bd0959062195c51ed93d0088b6f92051fc99050ece2538749165976233697ab4b610385366e5ce0b02ad6b61c168ecfbedcdf74278a38de340fd7a5fead8e588e294795f9b011e2e60377a89e25c90e145397cdeabc60fd32444a6b7642a611a83c464d8b8976666351b4865c37b02e6dc21dbcdf5f930341707b618cc0f03c3122646b3385c9df9f2ec730eec9d49e7dfc9153b6e6289da8c4f0ebea9ccc1b751948e3bb7171c9e4d57423b0eeeb79095c030cb52677b3f7e0b45c30f645391f3f9c957afa549c4e0b2465b03c67993cd200b1af01035962edbc4c9e89b31c82ac121987d6529dafdeef67a132dc04b6dc68e77f22862040b75e2ceb9ff16da0fca534e6db7bd12fa7b7f51b6c08c1e23dfcdb7acbd2da0b51c87ffbced065a612e9b1c8bba9b7e2d8d7a2f04fcc4aaf355b60d764879a76b5e16762d5f2f55d585d0c8e82df6940960cddfb72c91dfa71f6b4e1c6ca25dfc39a878e998a663c04fe29d5e83b9586d047b4d7ff70a9f0d44f127e7d741685ca75f11629128d916a0ffef4be586a30c4b70389cc746e84ebf177c01ee8a4511cfbb9d1ecf7f7b33c7dd8177896e10bbc82f838dcd6db7ac67de62bf46b6a640fb580c5d1d2708f3862e3d2b645d0d18e49ef088053e3a220adc0e033c2afcfe61c90e32151152eb3caaf746c5e377d541cafc6cbb0cc0fa48b5caf1728f2e1957f5addfc234f1a9d89e40d49356c9172d0561a695fce6dab1d412321bbf407f63766ffd7b6b3d79bcfa07991c5a9709849c1008689e3b47c50d613980bec239fb64185249d055b30375ccb4354d71fe4d05648fbf6c80634dfc3575f2f24abb714c1e4c95e8896763bf4316e954c7ad19e5780ab7a040ca6fb9271f90a8b22ae738daf6cb",
        .name = "nagydani-5-square",
        .gas = 17868
    },
    {
        .input = "000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000400c5a1611f8be90071a43db23cc2fe01871cc4c0e8ab5743f6378e4fef77f7f6db0095c0727e20225beb665645403453e325ad5f9aeb9ba99bf3c148f63f9c07cf4fe8847ad5242d6b7d4499f93bd47056ddab8f7dee878fc2314f344dbee2a7c41a5d3db91eff372c730c2fdd3a141a4b61999e36d549b9870cf2f4e632c4d5df5f024f81c028000073a0ed8847cfb0593d36a47142f578f05ccbe28c0c06aeb1b1da027794c48db880278f79ba78ae64eedfea3c07d10e0562668d839749dc95f40467d15cf65b9cfc52c7c4bcef1cda3596dd52631aac942f146c7cebd46065131699ce8385b0db1874336747ee020a5698a3d1a1082665721e769567f579830f9d259cec1a836845109c21cf6b25da572512bf3c42fd4b96e43895589042ab60dd41f497db96aec102087fe784165bb45f942859268fd2ff6c012d9d00c02ba83eace047cc5f7b2c392c2955c58a49f0338d6fc58749c9db2155522ac17914ec216ad87f12e0ee95574613942fa615898c4d9e8a3be68cd6afa4e7a003dedbdf8edfee31162b174f965b20ae752ad89c967b3068b6f722c16b354456ba8e280f987c08e0a52d40a2e8f3a59b94d590aeef01879eb7a90b3ee7d772c839c85519cbeaddc0c193ec4874a463b53fcaea3271d80ebfb39b33489365fc039ae549a17a9ff898eea2f4cb27b8dbee4c17b998438575b2b8d107e4a0d66ba7fca85b41a58a8d51f191a35c856dfbe8aef2b00048a694bbccff832d23c8ca7a7ff0b6c0b3011d00b97c86c0628444d267c951d9e4fb8f83e154b8f74fb51aa16535e498235c5597dac9606ed0be3173a3836baa4e7d756ffe1e2879b415d3846bccd538c05b847785699aefde3e305decb600cd8fb0e7d8de5efc26971a6ad4e6d7a2d91474f1023a0ac4b78dc937da0ce607a45974d2cac1c33a2631ff7fe6144a3b2e5cf98b531a9627dea92c1dc82204d09db0439b6a11dd64b484e1263aa45fd9539b6020b55e3baece3986a8bffc1003406348f5c61265099ed43a766ee4f93f5f9c5abbc32a0fd3ac2b35b87f9ec26037d88275bd7dd0a54474995ee34ed3727f3f97c48db544b1980193a4b76a8a3ddab3591ce527f16d91882e67f0103b5cda53f7da54d489fc4ac08b6ab358a5a04aa9daa16219d50bd672a7cb804ed769d218807544e5993f1c27427104b349906a0b654df0bf69328afd3013fbe430155339c39f236df5557bf92f1ded7ff609a8502f49064ec3d1dbfb6c15d3a4c11a4f8acd12278cbf68acd5709463d12e3338a6eddb8c112f199645e23154a8e60879d2a654e3ed9296aa28f134168619691cd2c6b9e2eba4438381676173fc63c2588a3c5910dc149cf3760f0aa9fa9c3f5faa9162b0bf1aac9dd32b706a60ef53cbdb394b6b40222b5bc80eea82ba8958386672564cae3794f977871ab62337cf03e30049201ec12937e7ce79d0f55d9c810e20acf52212aca1d3888949e0e4830aad88d804161230eb89d4d329cc83570fe257217d2119134048dd2ed167646975fc7d77136919a049ea74cf08ddd2b896890bb24a0ba18094a22baa351bf29ad96c66bbb1a598f2ca391749620e62d61c3561a7d3653ccc8892c7b99baaf76bf836e2991cb06d6bc0514568ff0d1ec8bb4b3d6984f5eaefb17d3ea2893722375d3ddb8e389a8eef7d7d198f8e687d6a513983df906099f9a2d23f4f9dec6f8ef2f11fc0a21fac45353b94e00486f5e17d386af42502d09db33cf0cf28310e049c07e88682aeeb00cb833c5174266e62407a57583f1f88b304b7c6e0c84bbe1c0fd423072d37a5bd0aacf764229e5c7cd02473460ba3645cd8e8ae144065bf02d0dd238593d8e230354f67e0b2f23012c23274f80e3ee31e35e2606a4a3f31d94ab755e6d163cff52cbb36b6d0cc67ffc512aeed1dce4d7a0d70ce82f2baba12e8d514dc92a056f994adfb17b5b9712bd5186f27a2fda1f7039c5df2c8587fdc62f5627580c13234b55be4df3056050e2d1ef3218f0dd66cb05265fe1acfb0989d8213f2c19d1735a7cf3fa65d88dad5af52dc2bba22b7abf46c3bc77b5091baab9e8f0ddc4d5e581037de91a9f8dcbc69309be29cc815cf19a20a7585b8b3073edf51fc9baeb3e509b97fa4ecfd621e0fd57bd61cac1b895c03248ff12bdbc57509250df3517e8a3fe1d776836b34ab352b973d932ef708b14f7418f9eceb1d87667e61e3e758649cb083f01b133d37ab2f5afa96d6c84bcacf4efc3851ad308c1e7d9113624fce29fab460ab9d2a48d92cdb281103a5250ad44cb2ff6e67ac670c02fdafb3e0f1353953d6d7d5646ca1568dea55275a050ec501b7c6250444f7219f1ba7521ba3b93d089727ca5f3bbe0d6c1300b423377004954c5628fdb65770b18ced5c9b23a4a5a6d6ef25fe01b4ce278de0bcc4ed86e28a0a68818ffa40970128cf2c38740e80037984428c1bd5113f40ff47512ee6f4e4d8f9b8e8e1b3040d2928d003bd1c1329dc885302fbce9fa81c23b4dc49c7c82d29b52957847898676c89aa5d32b5b0e1c0d5a2b79a19d67562f407f19425687971a957375879d90c5f57c857136c17106c9ab1b99d80e69c8c954ed386493368884b55c939b8d64d26f643e800c56f90c01079d7c534e3b2b7ae352cefd3016da55f6a85eb803b85e2304915fd2001f77c74e28746293c46e4f5f0fd49cf988aafd0026b8e7a3bab2da5cdce1ea26c2e29ec03f4807fac432662b2d6c060be1c7be0e5489de69d0a6e03a4b9117f9244b34a0f1ecba89884f781c6320412413a00c4980287409a2a78c2cd7e65cecebbe4ec1c28cac4dd95f6998e78fc6f1392384331c9436aa10e10e2bf8ad2c4eafbcf276aa7bae64b74428911b3269c749338b0fc5075ad",
        .expected = "5f9c70ec884926a89461056ad20ac4c30155e817f807e4d3f5bb743d789c83386762435c3627773fa77da5144451f2a8aad8adba88e0b669f5377c5e9bad70e45c86fe952b613f015a9953b8a5de5eaee4566acf98d41e327d93a35bd5cef4607d025e58951167957df4ff9b1627649d3943805472e5e293d3efb687cfd1e503faafeb2840a3e3b3f85d016051a58e1c9498aab72e63b748d834b31eb05d85dcde65e27834e266b85c75cc4ec0135135e0601cb93eeeb6e0010c8ceb65c4c319623c5e573a2c8c9fbbf7df68a930beb412d3f4dfd146175484f45d7afaa0d2e60684af9b34730f7c8438465ad3e1d0c3237336722f2aa51095bd5759f4b8ab4dda111b684aa3dac62a761722e7ae43495b7709933512c81c4e3c9133a51f7ce9f2b51fcec064f65779666960b4e45df3900f54311f5613e8012dd1b8efd359eda31a778264c72aa8bb419d862734d769076bce2810011989a45374e5c5d8729fec21427f0bf397eacbb4220f603cf463a4b0c94efd858ffd9768cd60d6ce68d755e0fbad007ce5c2223d70c7018345a102e4ab3c60a13a9e7794303156d4c2063e919f2153c13961fb324c80b240742f47773a7a8e25b3e3fb19b00ce839346c6eb3c732fbc6b888df0b1fe0a3d07b053a2e9402c267b2d62f794d8a2840526e3ade15ce2264496ccd7519571dfde47f7a4bb16292241c20b2be59f3f8fb4f6383f232d838c5a22d8c95b6834d9d2ca493f5a505ebe8899503b0e8f9b19e6e2dd81c1628b80016d02097e0134de51054c4e7674824d4d758760fc52377d2cad145e259aa2ffaf54139e1a66b1e0c1c191e32ac59474c6b526f5b3ba07d3e5ec286eddf531fcd5292869be58c9f22ef91026159f7cf9d05ef66b4299f4da48cc1635bf2243051d342d378a22c83390553e873713c0454ce5f3234397111ac3fe3207b86f0ed9fc025c81903e1748103692074f83824fda6341be4f95ff00b0a9a208c267e12fa01825054cc0513629bf3dbb56dc5b90d4316f87654a8be18227978ea0a8a522760cad620d0d14fd38920fb7321314062914275a5f99f677145a6979b156bd82ecd36f23f8e1273cc2759ecc0b2c69d94dad5211d1bed939dd87ed9e07b91d49713a6e16ade0a98aea789f04994e318e4ff2c8a188cd8d43aeb52c6daa3bc29b4af50ea82a247c5cd67b573b34cbadcc0a376d3bbd530d50367b42705d870f2e27a8197ef46070528bfe408360faa2ebb8bf76e9f388572842bcb119f4d84ee34ae31f5cc594f23705a49197b181fb78ed1ec99499c690f843a4d0cf2e226d118e9372271054fbabdcc5c92ae9fefaef0589cd0e722eaf30c1703ec4289c7fd81beaa8a455ccee5298e31e2080c10c366a6fcf56f7d13582ad0bcad037c612b710fc595b70fbefaaca23623b60c6c39b11beb8e5843b6b3dac60f",
        .name = "nagydani-5-qube",
        .gas = 17868
    },
    {
        .input = "000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000030000000000000000000000000000000000000000000000000000000000000400c5a1611f8be90071a43db23cc2fe01871cc4c0e8ab5743f6378e4fef77f7f6db0095c0727e20225beb665645403453e325ad5f9aeb9ba99bf3c148f63f9c07cf4fe8847ad5242d6b7d4499f93bd47056ddab8f7dee878fc2314f344dbee2a7c41a5d3db91eff372c730c2fdd3a141a4b61999e36d549b9870cf2f4e632c4d5df5f024f81c028000073a0ed8847cfb0593d36a47142f578f05ccbe28c0c06aeb1b1da027794c48db880278f79ba78ae64eedfea3c07d10e0562668d839749dc95f40467d15cf65b9cfc52c7c4bcef1cda3596dd52631aac942f146c7cebd46065131699ce8385b0db1874336747ee020a5698a3d1a1082665721e769567f579830f9d259cec1a836845109c21cf6b25da572512bf3c42fd4b96e43895589042ab60dd41f497db96aec102087fe784165bb45f942859268fd2ff6c012d9d00c02ba83eace047cc5f7b2c392c2955c58a49f0338d6fc58749c9db2155522ac17914ec216ad87f12e0ee95574613942fa615898c4d9e8a3be68cd6afa4e7a003dedbdf8edfee31162b174f965b20ae752ad89c967b3068b6f722c16b354456ba8e280f987c08e0a52d40a2e8f3a59b94d590aeef01879eb7a90b3ee7d772c839c85519cbeaddc0c193ec4874a463b53fcaea3271d80ebfb39b33489365fc039ae549a17a9ff898eea2f4cb27b8dbee4c17b998438575b2b8d107e4a0d66ba7fca85b41a58a8d51f191a35c856dfbe8aef2b00048a694bbccff832d23c8ca7a7ff0b6c0b3011d00b97c86c0628444d267c951d9e4fb8f83e154b8f74fb51aa16535e498235c5597dac9606ed0be3173a3836baa4e7d756ffe1e2879b415d3846bccd538c05b847785699aefde3e305decb600cd8fb0e7d8de5efc26971a6ad4e6d7a2d91474f1023a0ac4b78dc937da0ce607a45974d2cac1c33a2631ff7fe6144a3b2e5cf98b531a9627dea92c1dc82204d09db0439b6a11dd64b484e1263aa45fd9539b6020b55e3baece3986a8bffc1003406348f5c61265099ed43a766ee4f93f5f9c5abbc32a0fd3ac2b35b87f9ec26037d88275bd7dd0a54474995ee34ed3727f3f97c48db544b1980193a4b76a8a3ddab3591ce527f16d91882e67f0103b5cda53f7da54d489fc4ac08b6ab358a5a04aa9daa16219d50bd672a7cb804ed769d218807544e5993f1c27427104b349906a0b654df0bf69328afd3013fbe430155339c39f236df5557bf92f1ded7ff609a8502f49064ec3d1dbfb6c15d3a4c11a4f8acd12278cbf68acd5709463d12e3338a6eddb8c112f199645e23154a8e60879d2a654e3ed9296aa28f134168619691cd2c6b9e2eba4438381676173fc63c2588a3c5910dc149cf3760f0aa9fa9c3f5faa9162b0bf1aac9dd32b706a60ef53cbdb394b6b40222b5bc80eea82ba8958386672564cae3794f977871ab62337cf010001e30049201ec12937e7ce79d0f55d9c810e20acf52212aca1d3888949e0e4830aad88d804161230eb89d4d329cc83570fe257217d2119134048dd2ed167646975fc7d77136919a049ea74cf08ddd2b896890bb24a0ba18094a22baa351bf29ad96c66bbb1a598f2ca391749620e62d61c3561a7d3653ccc8892c7b99baaf76bf836e2991cb06d6bc0514568ff0d1ec8bb4b3d6984f5eaefb17d3ea2893722375d3ddb8e389a8eef7d7d198f8e687d6a513983df906099f9a2d23f4f9dec6f8ef2f11fc0a21fac45353b94e00486f5e17d386af42502d09db33cf0cf28310e049c07e88682aeeb00cb833c5174266e62407a57583f1f88b304b7c6e0c84bbe1c0fd423072d37a5bd0aacf764229e5c7cd02473460ba3645cd8e8ae144065bf02d0dd238593d8e230354f67e0b2f23012c23274f80e3ee31e35e2606a4a3f31d94ab755e6d163cff52cbb36b6d0cc67ffc512aeed1dce4d7a0d70ce82f2baba12e8d514dc92a056f994adfb17b5b9712bd5186f27a2fda1f7039c5df2c8587fdc62f5627580c13234b55be4df3056050e2d1ef3218f0dd66cb05265fe1acfb0989d8213f2c19d1735a7cf3fa65d88dad5af52dc2bba22b7abf46c3bc77b5091baab9e8f0ddc4d5e581037de91a9f8dcbc69309be29cc815cf19a20a7585b8b3073edf51fc9baeb3e509b97fa4ecfd621e0fd57bd61cac1b895c03248ff12bdbc57509250df3517e8a3fe1d776836b34ab352b973d932ef708b14f7418f9eceb1d87667e61e3e758649cb083f01b133d37ab2f5afa96d6c84bcacf4efc3851ad308c1e7d9113624fce29fab460ab9d2a48d92cdb281103a5250ad44cb2ff6e67ac670c02fdafb3e0f1353953d6d7d5646ca1568dea55275a050ec501b7c6250444f7219f1ba7521ba3b93d089727ca5f3bbe0d6c1300b423377004954c5628fdb65770b18ced5c9b23a4a5a6d6ef25fe01b4ce278de0bcc4ed86e28a0a68818ffa40970128cf2c38740e80037984428c1bd5113f40ff47512ee6f4e4d8f9b8e8e1b3040d2928d003bd1c1329dc885302fbce9fa81c23b4dc49c7c82d29b52957847898676c89aa5d32b5b0e1c0d5a2b79a19d67562f407f19425687971a957375879d90c5f57c857136c17106c9ab1b99d80e69c8c954ed386493368884b55c939b8d64d26f643e800c56f90c01079d7c534e3b2b7ae352cefd3016da55f6a85eb803b85e2304915fd2001f77c74e28746293c46e4f5f0fd49cf988aafd0026b8e7a3bab2da5cdce1ea26c2e29ec03f4807fac432662b2d6c060be1c7be0e5489de69d0a6e03a4b9117f9244b34a0f1ecba89884f781c6320412413a00c4980287409a2a78c2cd7e65cecebbe4ec1c28cac4dd95f6998e78fc6f1392384331c9436aa10e10e2bf8ad2c4eafbcf276aa7bae64b74428911b3269c749338b0fc5075ad",
        .expected = "5a0eb2bdf0ac1cae8e586689fa16cd4b07dfdedaec8a110ea1fdb059dd5253231b6132987598dfc6e11f86780428982d50cf68f67ae452622c3b336b537ef3298ca645e8f89ee39a26758206a5a3f6409afc709582f95274b57b71fae5c6b74619ae6f089a5393c5b79235d9caf699d23d88fb873f78379690ad8405e34c19f5257d596580c7a6a7206a3712825afe630c76b31cdb4a23e7f0632e10f14f4e282c81a66451a26f8df2a352b5b9f607a7198449d1b926e27036810368e691a74b91c61afa73d9d3b99453e7c8b50fd4f09c039a2f2feb5c419206694c31b92df1d9586140cb3417b38d0c503c7b508cc2ed12e813a1c795e9829eb39ee78eeaf360a169b491a1d4e419574e712402de9d48d54c1ae5e03739b7156615e8267e1fb0a897f067afd11fb33f6e24182d7aaaaa18fe5bc1982f20d6b871e5a398f0f6f718181d31ec225cfa9a0a70124ed9a70031bdf0c1c7829f708b6e17d50419ef361cf77d99c85f44607186c8d683106b8bd38a49b5d0fb503b397a83388c5678dcfcc737499d84512690701ed621a6f0172aecf037184ddf0f2453e4053024018e5ab2e30d6d5363b56e8b41509317c99042f517247474ab3abc848e00a07f69c254f46f2a05cf6ed84e5cc906a518fdcfdf2c61ce731f24c5264f1a25fc04934dc28aec112134dd523f70115074ca34e3807aa4cb925147f3a0ce152d323bd8c675ace446d0fd1ae30c4b57f0eb2c23884bc18f0964c0114796c5b6d080c3d89175665fbf63a6381a6a9da39ad070b645c8bb1779506da14439a9f5b5d481954764ea114fac688930bc68534d403cff4210673b6a6ff7ae416b7cd41404c3d3f282fcd193b86d0f54d0006c2a503b40d5c3930da980565b8f9630e9493a79d1c03e74e5f93ac8e4dc1a901ec5e3b3e57049124c7b72ea345aa359e782285d9e6a5c144a378111dd02c40855ff9c2be9b48425cb0b2fd62dc8678fd151121cf26a65e917d65d8e0dacfae108eb5508b601fb8ffa370be1f9a8b749a2d12eeab81f41079de87e2d777994fa4d28188c579ad327f9957fb7bdecec5c680844dd43cb57cf87aeb763c003e65011f73f8c63442df39a92b946a6bd968a1c1e4d5fa7d88476a68bd8e20e5b70a99259c7d3f85fb1b65cd2e93972e6264e74ebf289b8b6979b9b68a85cd5b360c1987f87235c3c845d62489e33acf85d53fa3561fe3a3aee18924588d9c6eba4edb7a4d106b31173e42929f6f0c48c80ce6a72d54eca7c0fe870068b7a7c89c63cdda593f5b32d3cb4ea8a32c39f00ab449155757172d66763ed9527019d6de6c9f2416aa6203f4d11c9ebee1e1d3845099e55504446448027212616167eb36035726daa7698b075286f5379cd3e93cb3e0cf4f9cb8d017facbb5550ed32d5ec5400ae57e47e2bf78d1eaeff9480cc765ceff39db500",
        .name = "nagydani-5-pow0x10001",
        .gas = 285900
    }
};

// clang-format on

TEST(SpuriousDragonThroughByzantium, modular_exponentiation)
{
    do_geth_tests<EVMC_BYZANTIUM>(
        "Modular Exponentiation", MODEXP_BYZANTIUM_TEST_CASES, 0x05_address);
}

// clang-format off
static const std::vector<test_case> BNADD_BYZANTIUM_TEST_CASES =
{
    {
        .input = "18b18acfb4c2c30276db5411368e7185b311dd124691610c5d3b74034e093dc9063c909c4720840cb5134cb9f59fa749755796819658d32efc0d288198f3726607c2b7f58a84bd6145f00c9c2bc0bb1a187f20ff2c92963a88019e7c6a014eed06614e20c147e940f2d70da3f74c9a17df361706a4485c742bd6788478fa17d7",
        .expected = "2243525c5efd4b9c3d3c45ac0ca3fe4dd85e830a4ce6b65fa1eeaee202839703301d1d33be6da8e509df21cc35964723180eed7532537db9ae5e7d48f195c915",
        .name = "chfast1",
        .gas = 500,
    },
    {
        .input = "2243525c5efd4b9c3d3c45ac0ca3fe4dd85e830a4ce6b65fa1eeaee202839703301d1d33be6da8e509df21cc35964723180eed7532537db9ae5e7d48f195c91518b18acfb4c2c30276db5411368e7185b311dd124691610c5d3b74034e093dc9063c909c4720840cb5134cb9f59fa749755796819658d32efc0d288198f37266",
        .expected = "2bd3e6d0f3b142924f5ca7b49ce5b9d54c4703d7ae5648e61d02268b1a0a9fb721611ce0a6af85915e2f1d70300909ce2e49dfad4a4619c8390cae66cefdb204",
        .name = "chfast2",
        .gas = 500,
    },
    {
        .input = "0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000",
        .expected = "00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000",
        .name = "cdetrio1",
        .gas = 500,
    },
    {
        .input = "00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000",
        .expected = "00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000",
        .name = "cdetrio2",
        .gas = 500,
    },
    {
        .input = "0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000",
        .expected = "00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000",
        .name = "cdetrio3",
        .gas = 500,
    },
    {
        .input = "",
        .expected = "00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000",
        .name = "cdetrio4",
        .gas = 500,
    },
    {
        .input = "000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000",
        .expected = "00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000",
        .name = "cdetrio5",
        .gas = 500,
    },
    {
        .input = "0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000002",
        .expected = "00000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000002",
        .name = "cdetrio6",
        .gas = 500,
    },
    {
        .input = "000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000",
        .expected = "00000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000002",
        .name = "cdetrio7",
        .gas = 500,
    },
    {
        .input = "00000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000002",
        .expected = "00000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000002",
        .name = "cdetrio8",
        .gas = 500,
    },
    {
        .input = "0000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000",
        .expected = "00000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000002",
        .name = "cdetrio9",
        .gas = 500,
    },
    {
        .input = "000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000",
        .expected = "00000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000002",
        .name = "cdetrio10",
        .gas = 500,
    },
    {
        .input = "0000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000002",
        .expected = "030644e72e131a029b85045b68181585d97816a916871ca8d3c208c16d87cfd315ed738c0e0a7c92e7845f96b2ae9c0a68a6a449e3538fc7ff3ebf7a5a18a2c4",
        .name = "cdetrio11",
        .gas = 500,
    },
    {
        .input = "000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000",
        .expected = "030644e72e131a029b85045b68181585d97816a916871ca8d3c208c16d87cfd315ed738c0e0a7c92e7845f96b2ae9c0a68a6a449e3538fc7ff3ebf7a5a18a2c4",
        .name = "cdetrio12",
        .gas = 500,
    },
    {
        .input = "17c139df0efee0f766bc0204762b774362e4ded88953a39ce849a8a7fa163fa901e0559bacb160664764a357af8a9fe70baa9258e0b959273ffc5718c6d4cc7c039730ea8dff1254c0fee9c0ea777d29a9c710b7e616683f194f18c43b43b869073a5ffcc6fc7a28c30723d6e58ce577356982d65b833a5a5c15bf9024b43d98",
        .expected = "15bf2bb17880144b5d1cd2b1f46eff9d617bffd1ca57c37fb5a49bd84e53cf66049c797f9ce0d17083deb32b5e36f2ea2a212ee036598dd7624c168993d1355f",
        .name = "cdetrio13",
        .gas = 500,
    },
    {
        .input = "17c139df0efee0f766bc0204762b774362e4ded88953a39ce849a8a7fa163fa901e0559bacb160664764a357af8a9fe70baa9258e0b959273ffc5718c6d4cc7c17c139df0efee0f766bc0204762b774362e4ded88953a39ce849a8a7fa163fa92e83f8d734803fc370eba25ed1f6b8768bd6d83887b87165fc2434fe11a830cb00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000",
        .expected = "00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000",
        .name = "cdetrio14",
        .gas = 500,
    }
};

// clang-format on

TEST(SpuriousDragonThroughByzantium, bn_add)
{
    do_geth_tests<EVMC_BYZANTIUM>(
        "bn_add", BNADD_BYZANTIUM_TEST_CASES, 0x06_address);
}

// clang-format off
static const std::vector<test_case> BNMUL_BYZANTIUM_TEST_CASES =
{
    {
        .input = "2bd3e6d0f3b142924f5ca7b49ce5b9d54c4703d7ae5648e61d02268b1a0a9fb721611ce0a6af85915e2f1d70300909ce2e49dfad4a4619c8390cae66cefdb20400000000000000000000000000000000000000000000000011138ce750fa15c2",
        .expected = "070a8d6a982153cae4be29d434e8faef8a47b274a053f5a4ee2a6c9c13c31e5c031b8ce914eba3a9ffb989f9cdd5b0f01943074bf4f0f315690ec3cec6981afc",
        .name = "chfast1",
        .gas = 40'000,
    },
    {
        .input = "070a8d6a982153cae4be29d434e8faef8a47b274a053f5a4ee2a6c9c13c31e5c031b8ce914eba3a9ffb989f9cdd5b0f01943074bf4f0f315690ec3cec6981afc30644e72e131a029b85045b68181585d97816a916871ca8d3c208c16d87cfd46",
        .expected = "025a6f4181d2b4ea8b724290ffb40156eb0adb514c688556eb79cdea0752c2bb2eff3f31dea215f1eb86023a133a996eb6300b44da664d64251d05381bb8a02e",
        .name = "chfast2",
        .gas = 40'000,
    },
    {
        .input = "025a6f4181d2b4ea8b724290ffb40156eb0adb514c688556eb79cdea0752c2bb2eff3f31dea215f1eb86023a133a996eb6300b44da664d64251d05381bb8a02e183227397098d014dc2822db40c0ac2ecbc0b548b438e5469e10460b6c3e7ea3",
        .expected = "14789d0d4a730b354403b5fac948113739e276c23e0258d8596ee72f9cd9d3230af18a63153e0ec25ff9f2951dd3fa90ed0197bfef6e2a1a62b5095b9d2b4a27",
        .name = "chfast3",
        .gas = 40'000,
    },
    {
        .input = "1a87b0584ce92f4593d161480614f2989035225609f08058ccfa3d0f940febe31a2f3c951f6dadcc7ee9007dff81504b0fcd6d7cf59996efdc33d92bf7f9f8f6ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff",
        .expected = "2cde5879ba6f13c0b5aa4ef627f159a3347df9722efce88a9afbb20b763b4c411aa7e43076f6aee272755a7f9b84832e71559ba0d2e0b17d5f9f01755e5b0d11",
        .name = "cdetrio1",
        .gas = 40'000,
    },
    {
        .input = "1a87b0584ce92f4593d161480614f2989035225609f08058ccfa3d0f940febe31a2f3c951f6dadcc7ee9007dff81504b0fcd6d7cf59996efdc33d92bf7f9f8f630644e72e131a029b85045b68181585d2833e84879b9709143e1f593f0000000",
        .expected = "1a87b0584ce92f4593d161480614f2989035225609f08058ccfa3d0f940febe3163511ddc1c3f25d396745388200081287b3fd1472d8339d5fecb2eae0830451",
        .name = "cdetrio2",
        .gas = 40'000,
    },
    {
        .input = "1a87b0584ce92f4593d161480614f2989035225609f08058ccfa3d0f940febe31a2f3c951f6dadcc7ee9007dff81504b0fcd6d7cf59996efdc33d92bf7f9f8f60000000000000000000000000000000100000000000000000000000000000000",
        .expected = "1051acb0700ec6d42a88215852d582efbaef31529b6fcbc3277b5c1b300f5cf0135b2394bb45ab04b8bd7611bd2dfe1de6a4e6e2ccea1ea1955f577cd66af85b",
        .name = "cdetrio3",
        .gas = 40'000,
    },
    {
        .input = "1a87b0584ce92f4593d161480614f2989035225609f08058ccfa3d0f940febe31a2f3c951f6dadcc7ee9007dff81504b0fcd6d7cf59996efdc33d92bf7f9f8f60000000000000000000000000000000000000000000000000000000000000009",
        .expected = "1dbad7d39dbc56379f78fac1bca147dc8e66de1b9d183c7b167351bfe0aeab742cd757d51289cd8dbd0acf9e673ad67d0f0a89f912af47ed1be53664f5692575",
        .name = "cdetrio4",
        .gas = 40'000,
    },
    {
        .input = "1a87b0584ce92f4593d161480614f2989035225609f08058ccfa3d0f940febe31a2f3c951f6dadcc7ee9007dff81504b0fcd6d7cf59996efdc33d92bf7f9f8f60000000000000000000000000000000000000000000000000000000000000001",
        .expected = "1a87b0584ce92f4593d161480614f2989035225609f08058ccfa3d0f940febe31a2f3c951f6dadcc7ee9007dff81504b0fcd6d7cf59996efdc33d92bf7f9f8f6",
        .name = "cdetrio5",
        .gas = 40'000,
    },
    {
        .input = "17c139df0efee0f766bc0204762b774362e4ded88953a39ce849a8a7fa163fa901e0559bacb160664764a357af8a9fe70baa9258e0b959273ffc5718c6d4cc7cffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff",
        .expected = "29e587aadd7c06722aabba753017c093f70ba7eb1f1c0104ec0564e7e3e21f6022b1143f6a41008e7755c71c3d00b6b915d386de21783ef590486d8afa8453b1",
        .name = "cdetrio6",
        .gas = 40'000,
    },
    {
        .input = "17c139df0efee0f766bc0204762b774362e4ded88953a39ce849a8a7fa163fa901e0559bacb160664764a357af8a9fe70baa9258e0b959273ffc5718c6d4cc7c30644e72e131a029b85045b68181585d2833e84879b9709143e1f593f0000000",
        .expected = "17c139df0efee0f766bc0204762b774362e4ded88953a39ce849a8a7fa163fa92e83f8d734803fc370eba25ed1f6b8768bd6d83887b87165fc2434fe11a830cb",
        .name = "cdetrio7",
        .gas = 40'000,
    },
    {
        .input = "17c139df0efee0f766bc0204762b774362e4ded88953a39ce849a8a7fa163fa901e0559bacb160664764a357af8a9fe70baa9258e0b959273ffc5718c6d4cc7c0000000000000000000000000000000100000000000000000000000000000000",
        .expected = "221a3577763877920d0d14a91cd59b9479f83b87a653bb41f82a3f6f120cea7c2752c7f64cdd7f0e494bff7b60419f242210f2026ed2ec70f89f78a4c56a1f15",
        .name = "cdetrio8",
        .gas = 40'000,
    },
    {
        .input = "17c139df0efee0f766bc0204762b774362e4ded88953a39ce849a8a7fa163fa901e0559bacb160664764a357af8a9fe70baa9258e0b959273ffc5718c6d4cc7c0000000000000000000000000000000000000000000000000000000000000009",
        .expected = "228e687a379ba154554040f8821f4e41ee2be287c201aa9c3bc02c9dd12f1e691e0fd6ee672d04cfd924ed8fdc7ba5f2d06c53c1edc30f65f2af5a5b97f0a76a",
        .name = "cdetrio9",
        .gas = 40'000,
    },
    {
        .input = "17c139df0efee0f766bc0204762b774362e4ded88953a39ce849a8a7fa163fa901e0559bacb160664764a357af8a9fe70baa9258e0b959273ffc5718c6d4cc7c0000000000000000000000000000000000000000000000000000000000000001",
        .expected = "17c139df0efee0f766bc0204762b774362e4ded88953a39ce849a8a7fa163fa901e0559bacb160664764a357af8a9fe70baa9258e0b959273ffc5718c6d4cc7c",
        .name = "cdetrio10",
        .gas = 40'000,
    },
    {
        .input = "039730ea8dff1254c0fee9c0ea777d29a9c710b7e616683f194f18c43b43b869073a5ffcc6fc7a28c30723d6e58ce577356982d65b833a5a5c15bf9024b43d98ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff",
        .expected = "00a1a234d08efaa2616607e31eca1980128b00b415c845ff25bba3afcb81dc00242077290ed33906aeb8e42fd98c41bcb9057ba03421af3f2d08cfc441186024",
        .name = "cdetrio11",
        .gas = 40'000,
    },
    {
        .input = "039730ea8dff1254c0fee9c0ea777d29a9c710b7e616683f194f18c43b43b869073a5ffcc6fc7a28c30723d6e58ce577356982d65b833a5a5c15bf9024b43d9830644e72e131a029b85045b68181585d2833e84879b9709143e1f593f0000000",
        .expected = "039730ea8dff1254c0fee9c0ea777d29a9c710b7e616683f194f18c43b43b8692929ee761a352600f54921df9bf472e66217e7bb0cee9032e00acc86b3c8bfaf",
        .name = "cdetrio12",
        .gas = 40'000,
    },
    {
        .input = "039730ea8dff1254c0fee9c0ea777d29a9c710b7e616683f194f18c43b43b869073a5ffcc6fc7a28c30723d6e58ce577356982d65b833a5a5c15bf9024b43d980000000000000000000000000000000100000000000000000000000000000000",
        .expected = "1071b63011e8c222c5a771dfa03c2e11aac9666dd097f2c620852c3951a4376a2f46fe2f73e1cf310a168d56baa5575a8319389d7bfa6b29ee2d908305791434",
        .name = "cdetrio13",
        .gas = 40'000,
    },
    {
        .input = "039730ea8dff1254c0fee9c0ea777d29a9c710b7e616683f194f18c43b43b869073a5ffcc6fc7a28c30723d6e58ce577356982d65b833a5a5c15bf9024b43d980000000000000000000000000000000000000000000000000000000000000009",
        .expected = "19f75b9dd68c080a688774a6213f131e3052bd353a304a189d7a2ee367e3c2582612f545fb9fc89fde80fd81c68fc7dcb27fea5fc124eeda69433cf5c46d2d7f",
        .name = "cdetrio14",
        .gas = 40'000,
    },
    {
        .input = "039730ea8dff1254c0fee9c0ea777d29a9c710b7e616683f194f18c43b43b869073a5ffcc6fc7a28c30723d6e58ce577356982d65b833a5a5c15bf9024b43d980000000000000000000000000000000000000000000000000000000000000001",
        .expected = "039730ea8dff1254c0fee9c0ea777d29a9c710b7e616683f194f18c43b43b869073a5ffcc6fc7a28c30723d6e58ce577356982d65b833a5a5c15bf9024b43d98",
        .name = "cdetrio15",
        .gas = 40'000,
    },
    {
        .input = "039730ea8dff1254c0fee9c0ea777d29a9c710b7e616683f194f18c43b43b869073a5ffcc6fc7a28c30723d6e58ce577356982d65b833a5a5c15bf9024b43d980000000000000000000000000000000000000000000000000000000000000000",
        .expected = "00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000",
        .name = "zeroScalar",
        .gas = 40'000,
    }
};

// clang-format on

TEST(SpuriousDragonThroughByzantium, bn_mul)
{
    do_geth_tests<EVMC_BYZANTIUM>(
        "bn_mul", BNMUL_BYZANTIUM_TEST_CASES, 0x07_address);
}

// clang-format off
static const std::vector<test_case> BNPAIRING_BYZANTIUM_TEST_CASES =
{
    {
        .input = "1c76476f4def4bb94541d57ebba1193381ffa7aa76ada664dd31c16024c43f593034dd2920f673e204fee2811c678745fc819b55d3e9d294e45c9b03a76aef41209dd15ebff5d46c4bd888e51a93cf99a7329636c63514396b4a452003a35bf704bf11ca01483bfa8b34b43561848d28905960114c8ac04049af4b6315a416782bb8324af6cfc93537a2ad1a445cfd0ca2a71acd7ac41fadbf933c2a51be344d120a2a4cf30c1bf9845f20c6fe39e07ea2cce61f0c9bb048165fe5e4de877550111e129f1cf1097710d41c4ac70fcdfa5ba2023c6ff1cbeac322de49d1b6df7c2032c61a830e3c17286de9462bf242fca2883585b93870a73853face6a6bf411198e9393920d483a7260bfb731fb5d25f1aa493335a9e71297e485b7aef312c21800deef121f1e76426a00665e5c4479674322d4f75edadd46debd5cd992f6ed090689d0585ff075ec9e99ad690c3395bc4b313370b38ef355acdadcd122975b12c85ea5db8c6deb4aab71808dcb408fe3d1e7690c43d37b4ce6cc0166fa7daa",
        .expected = "0000000000000000000000000000000000000000000000000000000000000001",
        .name = "jeff1",
        .gas = 260000,
    },
    {
        .input = "2eca0c7238bf16e83e7a1e6c5d49540685ff51380f309842a98561558019fc0203d3260361bb8451de5ff5ecd17f010ff22f5c31cdf184e9020b06fa5997db841213d2149b006137fcfb23036606f848d638d576a120ca981b5b1a5f9300b3ee2276cf730cf493cd95d64677bbb75fc42db72513a4c1e387b476d056f80aa75f21ee6226d31426322afcda621464d0611d226783262e21bb3bc86b537e986237096df1f82dff337dd5972e32a8ad43e28a78a96a823ef1cd4debe12b6552ea5f06967a1237ebfeca9aaae0d6d0bab8e28c198c5a339ef8a2407e31cdac516db922160fa257a5fd5b280642ff47b65eca77e626cb685c84fa6d3b6882a283ddd1198e9393920d483a7260bfb731fb5d25f1aa493335a9e71297e485b7aef312c21800deef121f1e76426a00665e5c4479674322d4f75edadd46debd5cd992f6ed090689d0585ff075ec9e99ad690c3395bc4b313370b38ef355acdadcd122975b12c85ea5db8c6deb4aab71808dcb408fe3d1e7690c43d37b4ce6cc0166fa7daa",
        .expected = "0000000000000000000000000000000000000000000000000000000000000001",
        .name = "jeff2",
        .gas = 260000,
    },
    {
        .input = "0f25929bcb43d5a57391564615c9e70a992b10eafa4db109709649cf48c50dd216da2f5cb6be7a0aa72c440c53c9bbdfec6c36c7d515536431b3a865468acbba2e89718ad33c8bed92e210e81d1853435399a271913a6520736a4729cf0d51eb01a9e2ffa2e92599b68e44de5bcf354fa2642bd4f26b259daa6f7ce3ed57aeb314a9a87b789a58af499b314e13c3d65bede56c07ea2d418d6874857b70763713178fb49a2d6cd347dc58973ff49613a20757d0fcc22079f9abd10c3baee245901b9e027bd5cfc2cb5db82d4dc9677ac795ec500ecd47deee3b5da006d6d049b811d7511c78158de484232fc68daf8a45cf217d1c2fae693ff5871e8752d73b21198e9393920d483a7260bfb731fb5d25f1aa493335a9e71297e485b7aef312c21800deef121f1e76426a00665e5c4479674322d4f75edadd46debd5cd992f6ed090689d0585ff075ec9e99ad690c3395bc4b313370b38ef355acdadcd122975b12c85ea5db8c6deb4aab71808dcb408fe3d1e7690c43d37b4ce6cc0166fa7daa",
        .expected = "0000000000000000000000000000000000000000000000000000000000000001",
        .name = "jeff3",
        .gas = 260000,
    },
    {
        .input = "2f2ea0b3da1e8ef11914acf8b2e1b32d99df51f5f4f206fc6b947eae860eddb6068134ddb33dc888ef446b648d72338684d678d2eb2371c61a50734d78da4b7225f83c8b6ab9de74e7da488ef02645c5a16a6652c3c71a15dc37fe3a5dcb7cb122acdedd6308e3bb230d226d16a105295f523a8a02bfc5e8bd2da135ac4c245d065bbad92e7c4e31bf3757f1fe7362a63fbfee50e7dc68da116e67d600d9bf6806d302580dc0661002994e7cd3a7f224e7ddc27802777486bf80f40e4ca3cfdb186bac5188a98c45e6016873d107f5cd131f3a3e339d0375e58bd6219347b008122ae2b09e539e152ec5364e7e2204b03d11d3caa038bfc7cd499f8176aacbee1f39e4e4afc4bc74790a4a028aff2c3d2538731fb755edefd8cb48d6ea589b5e283f150794b6736f670d6a1033f9b46c6f5204f50813eb85c8dc4b59db1c5d39140d97ee4d2b36d99bc49974d18ecca3e7ad51011956051b464d9e27d46cc25e0764bb98575bd466d32db7b15f582b2d5c452b36aa394b789366e5e3ca5aabd415794ab061441e51d01e94640b7e3084a07e02c78cf3103c542bc5b298669f211b88da1679b0b64a63b7e0e7bfe52aae524f73a55be7fe70c7e9bfc94b4cf0da1213d2149b006137fcfb23036606f848d638d576a120ca981b5b1a5f9300b3ee2276cf730cf493cd95d64677bbb75fc42db72513a4c1e387b476d056f80aa75f21ee6226d31426322afcda621464d0611d226783262e21bb3bc86b537e986237096df1f82dff337dd5972e32a8ad43e28a78a96a823ef1cd4debe12b6552ea5f",
        .expected = "0000000000000000000000000000000000000000000000000000000000000001",
        .name = "jeff4",
        .gas = 340000,
    },
    {
        .input = "20a754d2071d4d53903e3b31a7e98ad6882d58aec240ef981fdf0a9d22c5926a29c853fcea789887315916bbeb89ca37edb355b4f980c9a12a94f30deeed30211213d2149b006137fcfb23036606f848d638d576a120ca981b5b1a5f9300b3ee2276cf730cf493cd95d64677bbb75fc42db72513a4c1e387b476d056f80aa75f21ee6226d31426322afcda621464d0611d226783262e21bb3bc86b537e986237096df1f82dff337dd5972e32a8ad43e28a78a96a823ef1cd4debe12b6552ea5f1abb4a25eb9379ae96c84fff9f0540abcfc0a0d11aeda02d4f37e4baf74cb0c11073b3ff2cdbb38755f8691ea59e9606696b3ff278acfc098fa8226470d03869217cee0a9ad79a4493b5253e2e4e3a39fc2df38419f230d341f60cb064a0ac290a3d76f140db8418ba512272381446eb73958670f00cf46f1d9e64cba057b53c26f64a8ec70387a13e41430ed3ee4a7db2059cc5fc13c067194bcc0cb49a98552fd72bd9edb657346127da132e5b82ab908f5816c826acb499e22f2412d1a2d70f25929bcb43d5a57391564615c9e70a992b10eafa4db109709649cf48c50dd2198a1f162a73261f112401aa2db79c7dab1533c9935c77290a6ce3b191f2318d198e9393920d483a7260bfb731fb5d25f1aa493335a9e71297e485b7aef312c21800deef121f1e76426a00665e5c4479674322d4f75edadd46debd5cd992f6ed090689d0585ff075ec9e99ad690c3395bc4b313370b38ef355acdadcd122975b12c85ea5db8c6deb4aab71808dcb408fe3d1e7690c43d37b4ce6cc0166fa7daa",
        .expected = "0000000000000000000000000000000000000000000000000000000000000001",
        .name = "jeff5",
        .gas = 340000,
    },
    {
        .input = "1c76476f4def4bb94541d57ebba1193381ffa7aa76ada664dd31c16024c43f593034dd2920f673e204fee2811c678745fc819b55d3e9d294e45c9b03a76aef41209dd15ebff5d46c4bd888e51a93cf99a7329636c63514396b4a452003a35bf704bf11ca01483bfa8b34b43561848d28905960114c8ac04049af4b6315a416782bb8324af6cfc93537a2ad1a445cfd0ca2a71acd7ac41fadbf933c2a51be344d120a2a4cf30c1bf9845f20c6fe39e07ea2cce61f0c9bb048165fe5e4de877550111e129f1cf1097710d41c4ac70fcdfa5ba2023c6ff1cbeac322de49d1b6df7c103188585e2364128fe25c70558f1560f4f9350baf3959e603cc91486e110936198e9393920d483a7260bfb731fb5d25f1aa493335a9e71297e485b7aef312c21800deef121f1e76426a00665e5c4479674322d4f75edadd46debd5cd992f6ed090689d0585ff075ec9e99ad690c3395bc4b313370b38ef355acdadcd122975b12c85ea5db8c6deb4aab71808dcb408fe3d1e7690c43d37b4ce6cc0166fa7daa",
        .expected = "0000000000000000000000000000000000000000000000000000000000000000",
        .name = "jeff6",
        .gas = 260000,
    },
    {
        .input = "",
        .expected = "0000000000000000000000000000000000000000000000000000000000000001",
        .name = "empty_data",
        .gas = 100000,
    },
    {
        .input = "00000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000002198e9393920d483a7260bfb731fb5d25f1aa493335a9e71297e485b7aef312c21800deef121f1e76426a00665e5c4479674322d4f75edadd46debd5cd992f6ed090689d0585ff075ec9e99ad690c3395bc4b313370b38ef355acdadcd122975b12c85ea5db8c6deb4aab71808dcb408fe3d1e7690c43d37b4ce6cc0166fa7daa",
        .expected = "0000000000000000000000000000000000000000000000000000000000000000",
        .name = "one_point",
        .gas = 180000,
    },
    {
        .input = "00000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000002198e9393920d483a7260bfb731fb5d25f1aa493335a9e71297e485b7aef312c21800deef121f1e76426a00665e5c4479674322d4f75edadd46debd5cd992f6ed090689d0585ff075ec9e99ad690c3395bc4b313370b38ef355acdadcd122975b12c85ea5db8c6deb4aab71808dcb408fe3d1e7690c43d37b4ce6cc0166fa7daa00000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000002198e9393920d483a7260bfb731fb5d25f1aa493335a9e71297e485b7aef312c21800deef121f1e76426a00665e5c4479674322d4f75edadd46debd5cd992f6ed275dc4a288d1afb3cbb1ac09187524c7db36395df7be3b99e673b13a075a65ec1d9befcd05a5323e6da4d435f3b617cdb3af83285c2df711ef39c01571827f9d",
        .expected = "0000000000000000000000000000000000000000000000000000000000000001",
        .name = "two_point_match_2",
        .gas = 260000,
    },
    {
        .input = "00000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000002203e205db4f19b37b60121b83a7333706db86431c6d835849957ed8c3928ad7927dc7234fd11d3e8c36c59277c3e6f149d5cd3cfa9a62aee49f8130962b4b3b9195e8aa5b7827463722b8c153931579d3505566b4edf48d498e185f0509de15204bb53b8977e5f92a0bc372742c4830944a59b4fe6b1c0466e2a6dad122b5d2e030644e72e131a029b85045b68181585d97816a916871ca8d3c208c16d87cfd31a76dae6d3272396d0cbe61fced2bc532edac647851e3ac53ce1cc9c7e645a83198e9393920d483a7260bfb731fb5d25f1aa493335a9e71297e485b7aef312c21800deef121f1e76426a00665e5c4479674322d4f75edadd46debd5cd992f6ed090689d0585ff075ec9e99ad690c3395bc4b313370b38ef355acdadcd122975b12c85ea5db8c6deb4aab71808dcb408fe3d1e7690c43d37b4ce6cc0166fa7daa",
        .expected = "0000000000000000000000000000000000000000000000000000000000000001",
        .name = "two_point_match_3",
        .gas = 260000,
    },
    {
        .input = "105456a333e6d636854f987ea7bb713dfd0ae8371a72aea313ae0c32c0bf10160cf031d41b41557f3e7e3ba0c51bebe5da8e6ecd855ec50fc87efcdeac168bcc0476be093a6d2b4bbf907172049874af11e1b6267606e00804d3ff0037ec57fd3010c68cb50161b7d1d96bb71edfec9880171954e56871abf3d93cc94d745fa114c059d74e5b6c4ec14ae5864ebe23a71781d86c29fb8fb6cce94f70d3de7a2101b33461f39d9e887dbb100f170a2345dde3c07e256d1dfa2b657ba5cd030427000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000021a2c3013d2ea92e13c800cde68ef56a294b883f6ac35d25f587c09b1b3c635f7290158a80cd3d66530f74dc94c94adb88f5cdb481acca997b6e60071f08a115f2f997f3dbd66a7afe07fe7862ce239edba9e05c5afff7f8a1259c9733b2dfbb929d1691530ca701b4a106054688728c9972c8512e9789e9567aae23e302ccd75",
        .expected = "0000000000000000000000000000000000000000000000000000000000000001",
        .name = "two_point_match_4",
        .gas = 260000,
    },
    {
        .input = "00000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000002198e9393920d483a7260bfb731fb5d25f1aa493335a9e71297e485b7aef312c21800deef121f1e76426a00665e5c4479674322d4f75edadd46debd5cd992f6ed090689d0585ff075ec9e99ad690c3395bc4b313370b38ef355acdadcd122975b12c85ea5db8c6deb4aab71808dcb408fe3d1e7690c43d37b4ce6cc0166fa7daa00000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000002198e9393920d483a7260bfb731fb5d25f1aa493335a9e71297e485b7aef312c21800deef121f1e76426a00665e5c4479674322d4f75edadd46debd5cd992f6ed275dc4a288d1afb3cbb1ac09187524c7db36395df7be3b99e673b13a075a65ec1d9befcd05a5323e6da4d435f3b617cdb3af83285c2df711ef39c01571827f9d00000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000002198e9393920d483a7260bfb731fb5d25f1aa493335a9e71297e485b7aef312c21800deef121f1e76426a00665e5c4479674322d4f75edadd46debd5cd992f6ed090689d0585ff075ec9e99ad690c3395bc4b313370b38ef355acdadcd122975b12c85ea5db8c6deb4aab71808dcb408fe3d1e7690c43d37b4ce6cc0166fa7daa00000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000002198e9393920d483a7260bfb731fb5d25f1aa493335a9e71297e485b7aef312c21800deef121f1e76426a00665e5c4479674322d4f75edadd46debd5cd992f6ed275dc4a288d1afb3cbb1ac09187524c7db36395df7be3b99e673b13a075a65ec1d9befcd05a5323e6da4d435f3b617cdb3af83285c2df711ef39c01571827f9d00000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000002198e9393920d483a7260bfb731fb5d25f1aa493335a9e71297e485b7aef312c21800deef121f1e76426a00665e5c4479674322d4f75edadd46debd5cd992f6ed090689d0585ff075ec9e99ad690c3395bc4b313370b38ef355acdadcd122975b12c85ea5db8c6deb4aab71808dcb408fe3d1e7690c43d37b4ce6cc0166fa7daa00000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000002198e9393920d483a7260bfb731fb5d25f1aa493335a9e71297e485b7aef312c21800deef121f1e76426a00665e5c4479674322d4f75edadd46debd5cd992f6ed275dc4a288d1afb3cbb1ac09187524c7db36395df7be3b99e673b13a075a65ec1d9befcd05a5323e6da4d435f3b617cdb3af83285c2df711ef39c01571827f9d00000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000002198e9393920d483a7260bfb731fb5d25f1aa493335a9e71297e485b7aef312c21800deef121f1e76426a00665e5c4479674322d4f75edadd46debd5cd992f6ed090689d0585ff075ec9e99ad690c3395bc4b313370b38ef355acdadcd122975b12c85ea5db8c6deb4aab71808dcb408fe3d1e7690c43d37b4ce6cc0166fa7daa00000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000002198e9393920d483a7260bfb731fb5d25f1aa493335a9e71297e485b7aef312c21800deef121f1e76426a00665e5c4479674322d4f75edadd46debd5cd992f6ed275dc4a288d1afb3cbb1ac09187524c7db36395df7be3b99e673b13a075a65ec1d9befcd05a5323e6da4d435f3b617cdb3af83285c2df711ef39c01571827f9d00000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000002198e9393920d483a7260bfb731fb5d25f1aa493335a9e71297e485b7aef312c21800deef121f1e76426a00665e5c4479674322d4f75edadd46debd5cd992f6ed090689d0585ff075ec9e99ad690c3395bc4b313370b38ef355acdadcd122975b12c85ea5db8c6deb4aab71808dcb408fe3d1e7690c43d37b4ce6cc0166fa7daa00000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000002198e9393920d483a7260bfb731fb5d25f1aa493335a9e71297e485b7aef312c21800deef121f1e76426a00665e5c4479674322d4f75edadd46debd5cd992f6ed275dc4a288d1afb3cbb1ac09187524c7db36395df7be3b99e673b13a075a65ec1d9befcd05a5323e6da4d435f3b617cdb3af83285c2df711ef39c01571827f9d",
        .expected = "0000000000000000000000000000000000000000000000000000000000000001",
        .name = "ten_point_match_1",
        .gas = 900000,
    },
    {
        .input = "00000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000002203e205db4f19b37b60121b83a7333706db86431c6d835849957ed8c3928ad7927dc7234fd11d3e8c36c59277c3e6f149d5cd3cfa9a62aee49f8130962b4b3b9195e8aa5b7827463722b8c153931579d3505566b4edf48d498e185f0509de15204bb53b8977e5f92a0bc372742c4830944a59b4fe6b1c0466e2a6dad122b5d2e030644e72e131a029b85045b68181585d97816a916871ca8d3c208c16d87cfd31a76dae6d3272396d0cbe61fced2bc532edac647851e3ac53ce1cc9c7e645a83198e9393920d483a7260bfb731fb5d25f1aa493335a9e71297e485b7aef312c21800deef121f1e76426a00665e5c4479674322d4f75edadd46debd5cd992f6ed090689d0585ff075ec9e99ad690c3395bc4b313370b38ef355acdadcd122975b12c85ea5db8c6deb4aab71808dcb408fe3d1e7690c43d37b4ce6cc0166fa7daa00000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000002203e205db4f19b37b60121b83a7333706db86431c6d835849957ed8c3928ad7927dc7234fd11d3e8c36c59277c3e6f149d5cd3cfa9a62aee49f8130962b4b3b9195e8aa5b7827463722b8c153931579d3505566b4edf48d498e185f0509de15204bb53b8977e5f92a0bc372742c4830944a59b4fe6b1c0466e2a6dad122b5d2e030644e72e131a029b85045b68181585d97816a916871ca8d3c208c16d87cfd31a76dae6d3272396d0cbe61fced2bc532edac647851e3ac53ce1cc9c7e645a83198e9393920d483a7260bfb731fb5d25f1aa493335a9e71297e485b7aef312c21800deef121f1e76426a00665e5c4479674322d4f75edadd46debd5cd992f6ed090689d0585ff075ec9e99ad690c3395bc4b313370b38ef355acdadcd122975b12c85ea5db8c6deb4aab71808dcb408fe3d1e7690c43d37b4ce6cc0166fa7daa00000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000002203e205db4f19b37b60121b83a7333706db86431c6d835849957ed8c3928ad7927dc7234fd11d3e8c36c59277c3e6f149d5cd3cfa9a62aee49f8130962b4b3b9195e8aa5b7827463722b8c153931579d3505566b4edf48d498e185f0509de15204bb53b8977e5f92a0bc372742c4830944a59b4fe6b1c0466e2a6dad122b5d2e030644e72e131a029b85045b68181585d97816a916871ca8d3c208c16d87cfd31a76dae6d3272396d0cbe61fced2bc532edac647851e3ac53ce1cc9c7e645a83198e9393920d483a7260bfb731fb5d25f1aa493335a9e71297e485b7aef312c21800deef121f1e76426a00665e5c4479674322d4f75edadd46debd5cd992f6ed090689d0585ff075ec9e99ad690c3395bc4b313370b38ef355acdadcd122975b12c85ea5db8c6deb4aab71808dcb408fe3d1e7690c43d37b4ce6cc0166fa7daa00000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000002203e205db4f19b37b60121b83a7333706db86431c6d835849957ed8c3928ad7927dc7234fd11d3e8c36c59277c3e6f149d5cd3cfa9a62aee49f8130962b4b3b9195e8aa5b7827463722b8c153931579d3505566b4edf48d498e185f0509de15204bb53b8977e5f92a0bc372742c4830944a59b4fe6b1c0466e2a6dad122b5d2e030644e72e131a029b85045b68181585d97816a916871ca8d3c208c16d87cfd31a76dae6d3272396d0cbe61fced2bc532edac647851e3ac53ce1cc9c7e645a83198e9393920d483a7260bfb731fb5d25f1aa493335a9e71297e485b7aef312c21800deef121f1e76426a00665e5c4479674322d4f75edadd46debd5cd992f6ed090689d0585ff075ec9e99ad690c3395bc4b313370b38ef355acdadcd122975b12c85ea5db8c6deb4aab71808dcb408fe3d1e7690c43d37b4ce6cc0166fa7daa00000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000002203e205db4f19b37b60121b83a7333706db86431c6d835849957ed8c3928ad7927dc7234fd11d3e8c36c59277c3e6f149d5cd3cfa9a62aee49f8130962b4b3b9195e8aa5b7827463722b8c153931579d3505566b4edf48d498e185f0509de15204bb53b8977e5f92a0bc372742c4830944a59b4fe6b1c0466e2a6dad122b5d2e030644e72e131a029b85045b68181585d97816a916871ca8d3c208c16d87cfd31a76dae6d3272396d0cbe61fced2bc532edac647851e3ac53ce1cc9c7e645a83198e9393920d483a7260bfb731fb5d25f1aa493335a9e71297e485b7aef312c21800deef121f1e76426a00665e5c4479674322d4f75edadd46debd5cd992f6ed090689d0585ff075ec9e99ad690c3395bc4b313370b38ef355acdadcd122975b12c85ea5db8c6deb4aab71808dcb408fe3d1e7690c43d37b4ce6cc0166fa7daa",
        .expected = "0000000000000000000000000000000000000000000000000000000000000001",
        .name = "ten_point_match_2",
        .gas = 900000,
    },
    {
        .input = "105456a333e6d636854f987ea7bb713dfd0ae8371a72aea313ae0c32c0bf10160cf031d41b41557f3e7e3ba0c51bebe5da8e6ecd855ec50fc87efcdeac168bcc0476be093a6d2b4bbf907172049874af11e1b6267606e00804d3ff0037ec57fd3010c68cb50161b7d1d96bb71edfec9880171954e56871abf3d93cc94d745fa114c059d74e5b6c4ec14ae5864ebe23a71781d86c29fb8fb6cce94f70d3de7a2101b33461f39d9e887dbb100f170a2345dde3c07e256d1dfa2b657ba5cd030427000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000021a2c3013d2ea92e13c800cde68ef56a294b883f6ac35d25f587c09b1b3c635f7290158a80cd3d66530f74dc94c94adb88f5cdb481acca997b6e60071f08a115f2f997f3dbd66a7afe07fe7862ce239edba9e05c5afff7f8a1259c9733b2dfbb929d1691530ca701b4a106054688728c9972c8512e9789e9567aae23e302ccd75",
        .expected = "0000000000000000000000000000000000000000000000000000000000000001",
        .name = "ten_point_match_3",
        .gas = 260000,
    }
};

// clang-format on

TEST(SpuriousDragonThroughByzantium, bn_pairing)
{
    do_geth_tests<EVMC_BYZANTIUM>(
        "bn_pairing", BNPAIRING_BYZANTIUM_TEST_CASES, 0x08_address);
}

TEST(Istanbul, ecrecover)
{
    do_basic_tests(
        "ecrecover", ECRECOVER_TEST_CASES, std::size(ECRECOVER_TEST_CASES));
}

TEST(Istanbul, sha256)
{
    do_basic_tests("sha256", SHA256_TEST_CASES, std::size(SHA256_TEST_CASES));
}

TEST(Istanbul, ripemd160)
{
    do_basic_tests(
        "ripemd160", RIPEMD160_TEST_CASES, std::size(RIPEMD160_TEST_CASES));
}

TEST(Istanbul, identity)
{
    do_basic_tests(
        "identity", IDENTITY_TEST_CASES, std::size(IDENTITY_TEST_CASES));
}

TEST(Istanbul, modular_exponentiation)
{
    // the modular exponentiation behavior did not change from the previous fork
    do_geth_tests<EVMC_ISTANBUL>(
        "Modular Exponentiation", MODEXP_BYZANTIUM_TEST_CASES, 0x05_address);
}

template <typename Callable>
auto transform_test_cases(std::vector<test_case> const &source, Callable &&f)
{
    auto res = source;
    for (auto &test_case : res) {
        f(test_case);
    }
    return res;
}

TEST(Istanbul, bn_add)
{
    do_geth_tests(
        "bn_add",
        transform_test_cases(
            BNADD_BYZANTIUM_TEST_CASES,
            [](test_case &test) { test.gas = 150; }),
        0x06_address);
}

TEST(Istanbul, bn_mul)
{
    do_geth_tests(
        "bn_mul",
        transform_test_cases(
            BNMUL_BYZANTIUM_TEST_CASES,
            [](test_case &test) { test.gas = 6'000; }),
        0x07_address);
}

auto make_bn_pairing_post_istanbul_tests()
{
    auto res = BNPAIRING_BYZANTIUM_TEST_CASES;
    res[0].gas = 113000;
    res[1].gas = 113000;
    res[2].gas = 113000;
    res[3].gas = 147000;
    res[4].gas = 147000;
    res[5].gas = 113000;
    res[6].gas = 45000;
    res[7].gas = 79000;
    res[8].gas = 113000;
    res[9].gas = 113000;
    res[10].gas = 113000;
    res[11].gas = 385000;
    res[12].gas = 385000;
    res[13].gas = 113000;
    return res;
}

TEST(Istanbul, bn_pairing)
{
    do_geth_tests(
        "bn_pairing", make_bn_pairing_post_istanbul_tests(), 0x08_address);
}

// clang-format off
static const std::vector<test_case> BLAKE2F_VALID_ISTANBUL_TEST_CASES =
{
    {
        .input = "0000000048c9bdf267e6096a3ba7ca8485ae67bb2bf894fe72f36e3cf1361d5f3af54fa5d182e6ad7f520e511f6c3e2b8c68059b6bbd41fbabd9831f79217e1319cde05b61626300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000300000000000000000000000000000001",
        .expected = "08c9bcf367e6096a3ba7ca8485ae67bb2bf894fe72f36e3cf1361d5f3af54fa5d282e6ad7f520e511f6c3e2b8c68059b9442be0454267ce079217e1319cde05b",
        .name = "vector 4",
        .gas = 0,
    },
    {
        .input = "0000000c48c9bdf267e6096a3ba7ca8485ae67bb2bf894fe72f36e3cf1361d5f3af54fa5d182e6ad7f520e511f6c3e2b8c68059b6bbd41fbabd9831f79217e1319cde05b61626300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000300000000000000000000000000000001",
        .expected = "ba80a53f981c4d0d6a2797b69f12f6e94c212f14685ac4b74b12bb6fdbffa2d17d87c5392aab792dc252d5de4533cc9518d38aa8dbf1925ab92386edd4009923",
        .name = "vector 5",
        .gas = 12,
    },
    {
        .input = "0000000c48c9bdf267e6096a3ba7ca8485ae67bb2bf894fe72f36e3cf1361d5f3af54fa5d182e6ad7f520e511f6c3e2b8c68059b6bbd41fbabd9831f79217e1319cde05b61626300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000300000000000000000000000000000000",
        .expected = "75ab69d3190a562c51aef8d88f1c2775876944407270c42c9844252c26d2875298743e7f6d5ea2f2d3e8d226039cd31b4e426ac4f2d3d666a610c2116fde4735",
        .name = "vector 6",
        .gas = 12,
    },
    {
        .input = "0000000148c9bdf267e6096a3ba7ca8485ae67bb2bf894fe72f36e3cf1361d5f3af54fa5d182e6ad7f520e511f6c3e2b8c68059b6bbd41fbabd9831f79217e1319cde05b61626300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000300000000000000000000000000000001",
        .expected = "b63a380cb2897d521994a85234ee2c181b5f844d2c624c002677e9703449d2fba551b3a8333bcdf5f2f7e08993d53923de3d64fcc68c034e717b9293fed7a421",
        .name = "vector 7",
        .gas = 1,
    },
    {
        .input = "007A120048c9bdf267e6096a3ba7ca8485ae67bb2bf894fe72f36e3cf1361d5f3af54fa5d182e6ad7f520e511f6c3e2b8c68059b6bbd41fbabd9831f79217e1319cde05b61626300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000300000000000000000000000000000001",
        .expected = "6d2ce9e534d50e18ff866ae92d70cceba79bbcd14c63819fe48752c8aca87a4bb7dcc230d22a4047f0486cfcfb50a17b24b2899eb8fca370f22240adb5170189",
        .name = "vector 8",
        .gas = 8000000,
    }
};

static const std::vector<test_case> BLAKE2F_INVALID_ISTANBUL_TEST_CASES =
{
    {
        .input = "",
        .expected = "",
        .name = "vector 0: empty input"
    },
    {
        .input = "00000c48c9bdf267e6096a3ba7ca8485ae67bb2bf894fe72f36e3cf1361d5f3af54fa5d182e6ad7f520e511f6c3e2b8c68059b6bbd41fbabd9831f79217e1319cde05b61626300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000300000000000000000000000000000001",
        .expected = "",
        .name = "vector 1: less than 213 bytes input"
    },
    {
        .input = "000000000c48c9bdf267e6096a3ba7ca8485ae67bb2bf894fe72f36e3cf1361d5f3af54fa5d182e6ad7f520e511f6c3e2b8c68059b6bbd41fbabd9831f79217e1319cde05b61626300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000300000000000000000000000000000001",
        .expected = "",
        .name = "vector 2: more than 213 bytes input"
    },
    {
        .input = "0000000c48c9bdf267e6096a3ba7ca8485ae67bb2bf894fe72f36e3cf1361d5f3af54fa5d182e6ad7f520e511f6c3e2b8c68059b6bbd41fbabd9831f79217e1319cde05b61626300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000300000000000000000000000000000002",
        .expected = "",
        .name = "vector 3: malformed final block indicator flag"
    }
};

// clang-format on

TEST(Istanbul, blake2f_valid)
{
    do_geth_tests(
        "blake_2f_valid", BLAKE2F_VALID_ISTANBUL_TEST_CASES, 0x09_address);
}

TEST(Istanbul, blake2f_invalid)
{
    do_geth_tests(
        "blake_2f_invalid", BLAKE2F_INVALID_ISTANBUL_TEST_CASES, 0x09_address);
}

TEST(Berlin, ecrecover)
{
    do_basic_tests(
        "ecrecover", ECRECOVER_TEST_CASES, std::size(ECRECOVER_TEST_CASES));
}

TEST(Berlin, sha256)
{
    do_basic_tests("sha256", SHA256_TEST_CASES, std::size(SHA256_TEST_CASES));
}

TEST(Berlin, ripemd160)
{
    do_basic_tests(
        "ripemd160", RIPEMD160_TEST_CASES, std::size(RIPEMD160_TEST_CASES));
}

TEST(Berlin, identity)
{
    do_basic_tests(
        "identity", IDENTITY_TEST_CASES, std::size(IDENTITY_TEST_CASES));
}

auto make_modexp_berlin_test_cases()
{
    auto res = MODEXP_BYZANTIUM_TEST_CASES;
    res[0].gas = 1360;
    res[1].gas = 1360;
    res[2].gas = 200;
    res[3].gas = 200;
    res[4].gas = 341;
    res[5].gas = 200;
    res[6].gas = 200;
    res[7].gas = 1365;
    res[8].gas = 341;
    res[9].gas = 341;
    res[10].gas = 5461;
    res[11].gas = 1365;
    res[12].gas = 1365;
    res[13].gas = 21845;
    res[14].gas = 5461;
    res[15].gas = 5461;
    res[16].gas = 87381;
    return res;
}

TEST(Berlin, modular_exponentiation)
{
    do_geth_tests(
        "Modular Exponentiation",
        make_modexp_berlin_test_cases(),
        0x05_address);
}

TEST(Berlin, bn_add)
{
    do_geth_tests(
        "bn_add",
        transform_test_cases(
            BNADD_BYZANTIUM_TEST_CASES,
            [](test_case &test) { test.gas = 150; }),
        0x06_address);
}

TEST(Berlin, bn_mul)
{
    do_geth_tests(
        "bn_mul",
        transform_test_cases(
            BNMUL_BYZANTIUM_TEST_CASES,
            [](test_case &test) { test.gas = 6'000; }),
        0x07_address);
}

TEST(Berlin, bn_pairing)
{
    do_geth_tests(
        "bn_pairing", make_bn_pairing_post_istanbul_tests(), 0x08_address);
}

TEST(Berlin, blake2f_valid)
{
    // the test cases did not change from the previous fork
    do_geth_tests(
        "blake_2f_valid", BLAKE2F_VALID_ISTANBUL_TEST_CASES, 0x09_address);
}

TEST(Berlin, blake2f_invalid)
{
    // the test cases did not change from the previous fork
    do_geth_tests(
        "blake_2f_invalid", BLAKE2F_INVALID_ISTANBUL_TEST_CASES, 0x09_address);
}


static const std::vector<test_case> BLS_G1_ADD_VALID_PRAGUE_TEST_CASES =
{
    {
        .input = "000000000000000000000000000000000572cbea904d67468808c8eb50a9450c9721db309128012543902d0ac358a62ae28f75bb8f1c7c42c39a8c5529bf0f4e00000000000000000000000000000000166a9d8cabc673a322fda673779d8e3822ba3ecb8670e461f73bb9021d5fd76a4c56d9d4cd16bd1bba86881979749d280000000000000000000000000000000009ece308f9d1f0131765212deca99697b112d61f9be9a5f1f3780a51335b3ff981747a0b2ca2179b96d2c0c9024e522400000000000000000000000000000000032b80d3a6f5b09f8a84623389c5f80ca69a0cddabc3097f9d9c27310fd43be6e745256c634af45ca3473b0590ae30d1",
        .expected = "0000000000000000000000000000000010e7791fb972fe014159aa33a98622da3cdc98ff707965e536d8636b5fcc5ac7a91a8c46e59a00dca575af0f18fb13dc0000000000000000000000000000000016ba437edcc6551e30c10512367494bfb6b01cc6681e8a4c3cd2501832ab5c4abc40b4578b85cbaffbf0bcd70d67c6e2",
        .name = "bls_g1add_(2*g1+3*g1=5*g1)",
        .gas = 375
    },
    {
        .input = "0000000000000000000000000000000017f1d3a73197d7942695638c4fa9ac0fc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bb0000000000000000000000000000000008b3f481e3aaa0f1a09e30ed741d8ae4fcf5e095d5d00af600db18cb2c04b3edd03cc744a2888ae40caa232946c5e7e10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000",
        .expected = "0000000000000000000000000000000017f1d3a73197d7942695638c4fa9ac0fc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bb0000000000000000000000000000000008b3f481e3aaa0f1a09e30ed741d8ae4fcf5e095d5d00af600db18cb2c04b3edd03cc744a2888ae40caa232946c5e7e1",
        .name = "bls_g1add_(inf+g1=g1)",
        .gas = 375
    },
    {
        .input = "00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000",
        .expected = "0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000",
        .name = "bls_g1add_(inf+inf=inf)",
        .gas = 375,
    },
    {
        .input = "0000000000000000000000000000000012196c5a43d69224d8713389285f26b98f86ee910ab3dd668e413738282003cc5b7357af9a7af54bb713d62255e80f560000000000000000000000000000000006ba8102bfbeea4416b710c73e8cce3032c31c6269c44906f8ac4f7874ce99fb17559992486528963884ce429a992fee000000000000000000000000000000000001101098f5c39893765766af4512a0c74e1bb89bc7e6fdf14e3e7337d257cc0f94658179d83320b99f31ff94cd2bac0000000000000000000000000000000003e1a9f9f44ca2cdab4f43a1a3ee3470fdf90b2fc228eb3b709fcd72f014838ac82a6d797aeefed9a0804b22ed1ce8f7",
        .expected = "000000000000000000000000000000001466e1373ae4a7e7ba885c5f0c3ccfa48cdb50661646ac6b779952f466ac9fc92730dcaed9be831cd1f8c4fefffd5209000000000000000000000000000000000c1fb750d2285d4ca0378e1e8cdbf6044151867c34a711b73ae818aee6dbe9e886f53d7928cc6ed9c851e0422f609b11",
        .name = "matter_g1_add_0",
        .gas = 375,
    },
    {
        .input = "00000000000000000000000000000000117dbe419018f67844f6a5e1b78a1e597283ad7b8ee7ac5e58846f5a5fd68d0da99ce235a91db3ec1cf340fe6b7afcdb0000000000000000000000000000000013316f23de032d25e912ae8dc9b54c8dba1be7cecdbb9d2228d7e8f652011d46be79089dd0a6080a73c82256ce5e4ed2000000000000000000000000000000000441e7f7f96198e4c23bd5eb16f1a7f045dbc8c53219ab2bcea91d3a027e2dfe659feac64905f8b9add7e4bfc91bec2b0000000000000000000000000000000005fc51bb1b40c87cd4292d4b66f8ca5ce4ef9abd2b69d4464b4879064203bda7c9fc3f896a3844ebc713f7bb20951d95",
        .expected = "0000000000000000000000000000000016b8ab56b45a9294466809b8e858c1ad15ad0d52cfcb62f8f5753dc94cee1de6efaaebce10701e3ec2ecaa9551024ea600000000000000000000000000000000124571eec37c0b1361023188d66ec17c1ec230d31b515e0e81e599ec19e40c8a7c8cdea9735bc3d8b4e37ca7e5dd71f6",
        .name = "matter_g1_add_1",
        .gas = 375,
    },
    {
        .input = "0000000000000000000000000000000008ab7b556c672db7883ec47efa6d98bb08cec7902ebb421aac1c31506b177ac444ffa2d9b400a6f1cbdc6240c607ee110000000000000000000000000000000016b7fa9adf4addc2192271ce7ad3c8d8f902d061c43b7d2e8e26922009b777855bffabe7ed1a09155819eabfa87f276f00000000000000000000000000000000114c3f11ba0b47551fa28f09f148936d6b290dc9f2d0534a83c32b0b849ab921ce6bcaa4ff3c917707798d9c74f2084f00000000000000000000000000000000149dc028207fb04a7795d94ea65e21f9952e445000eb954531ee519efde6901675d3d2446614d243efb77a9cfe0ca3ae",
        .expected = "0000000000000000000000000000000002ce7a08719448494857102da464bc65a47c95c77819af325055a23ac50b626df4732daf63feb9a663d71b7c9b8f2c510000000000000000000000000000000016117e87e9b55bd4bd5763d69d5240d30745e014b9aef87c498f9a9e3286ec4d5927df7cd5a2e54ac4179e78645acf27",
        .name = "matter_g1_add_2",
        .gas = 375,
    },
    {
        .input = "0000000000000000000000000000000015ff9a232d9b5a8020a85d5fe08a1dcfb73ece434258fe0e2fddf10ddef0906c42dcb5f5d62fc97f934ba900f17beb330000000000000000000000000000000009cfe4ee2241d9413c616462d7bac035a6766aeaab69c81e094d75b840df45d7e0dfac0265608b93efefb9a8728b98e4000000000000000000000000000000000c3d564ac1fe12f18f528c3750583ab6af8973bff3eded7bb4778c32805d9b17846cc7c687af0f46bc87de7748ab72980000000000000000000000000000000002f164c131cbd5afc85692c246157d38dc4bbb2959d2edfa6daf0a8b17c7a898aad53b400e8bdc2b29bf6688ee863db7",
        .expected = "0000000000000000000000000000000015510826f50b88fa369caf062ecdf8b03a67e660a35b219b44437a5583b5a9adf76991dce7bff9afc50257f847299504000000000000000000000000000000000a83e879895a1b47dbd6cd25ce8b719e7490cfe021614f7539e841fc2f9c09f071e386676de60b6579aa4bf6d37b13dd",
        .name = "matter_g1_add_3",
        .gas = 375,
    },
    {
        .input = "0000000000000000000000000000000017a17b82e3bfadf3250210d8ef572c02c3610d65ab4d7366e0b748768a28ee6a1b51f77ed686a64f087f36f641e7dca900000000000000000000000000000000077ea73d233ccea51dc4d5acecf6d9332bf17ae51598f4b394a5f62fb387e9c9aa1d6823b64a074f5873422ca57545d30000000000000000000000000000000019fe3a64361fea14936ff0b3e630471494d0c0b9423e6a004184a2965221c18849b5ed0eb2708a587323d8d6c6735a90000000000000000000000000000000000340823d314703e5efeb0a65c23069199d7dfff8793aaacb98cdcd6177fc8e61ab3294c57bf13b4406266715752ef3e6",
        .expected = "00000000000000000000000000000000010b1c96d3910f56b0bf54da5ae8c7ab674a07f8143b61fed660e7309e626dc73eaa2b11886cdb82e2b6735e7802cc860000000000000000000000000000000002dabbbedd72872c2c012e7e893d2f3df1834c43873315488d814ddd6bfcca6758a18aa6bd02a0f3aed962cb51f0a222",
        .name = "matter_g1_add_4",
        .gas = 375,
    },
    {
        .input = "000000000000000000000000000000000c1243478f4fbdc21ea9b241655947a28accd058d0cdb4f9f0576d32f09dddaf0850464550ff07cab5927b3e4c863ce90000000000000000000000000000000015fb54db10ffac0b6cd374eb7168a8cb3df0a7d5f872d8e98c1f623deb66df5dd08ff4c3658f2905ec8bd02598bd4f90000000000000000000000000000000001461565b03a86df363d1854b4af74879115dffabeddfa879e2c8db9aa414fb291a076c3bdf0beee82d9c094ea8dc381a000000000000000000000000000000000e19d51ab619ee2daf25ea5bfa51eb217eabcfe0b5cb0358fd2fa105fd7cb0f5203816b990df6fda4e0e8d541be9bcf6",
        .expected = "000000000000000000000000000000000cb40d0bf86a627d3973f1e7846484ffd0bc4943b42a54ff9527c285fed3c056b947a9b6115824cabafe13cd1af8181c00000000000000000000000000000000076255fc12f1a9dbd232025815238baaa6a3977fd87594e8d1606caec0d37b916e1e43ee2d2953d75a40a7ba416df237",
        .name = "matter_g1_add_5",
        .gas = 375,
    },
    {
        .input = "000000000000000000000000000000000328f09584b6d6c98a709fc22e184123994613aca95a28ac53df8523b92273eb6f4e2d9b2a7dcebb474604d54a210719000000000000000000000000000000001220ebde579911fe2e707446aaad8d3789fae96ae2e23670a4fd856ed82daaab704779eb4224027c1ed9460f39951a1b0000000000000000000000000000000019cabba3e09ad34cc3d125e0eb41b527aa48a4562c2b7637467b2dbc71c373897d50eed1bc75b2bde8904ece5626d6e400000000000000000000000000000000056b0746f820cff527358c86479dc924a10b9f7cae24cd495625a4159c8b71a8c3ad1a15ebf22d3561cd4b74e8a6e48b",
        .expected = "000000000000000000000000000000000e115e0b61c1f1b25cc10a7b3bd21cf696b1433a0c366c2e1bca3c26b09482c6eced8c8ecfa69ce6b9b3b4419779262e00000000000000000000000000000000077b85daf61b9f947e81633e3bc64e697bc6c1d873f2c21e5c4c3a11302d4d5ef4c3ff5519564729aaf2a50a3c9f1196",
        .name = "matter_g1_add_6",
        .gas = 375,
    },
    {
        .input = "0000000000000000000000000000000002ebfa98aa92c32a29ebe17fcb1819ba82e686abd9371fcee8ea793b4c72b6464085044f818f1f5902396df0122830cb00000000000000000000000000000000001184715b8432ed190b459113977289a890f68f6085ea111466af15103c9c02467da33e01d6bff87fd57db6ccba442a0000000000000000000000000000000011f649ee35ff8114060fc5e4df9ac828293f6212a9857ca31cb3e9ce49aa1212154a9808f1e763bc989b6d5ba7cf09390000000000000000000000000000000019af81eca7452f58c1a6e99fab50dc0d5eeebc7712153e717a14a31cffdfd0a923dbd585e652704a174905605a2e8b9d",
        .expected = "000000000000000000000000000000000013e37a8950a659265b285c6fb56930fb77759d9d40298acac2714b97b83ec7692a7d1c4ccb83f074384db9eedd809c0000000000000000000000000000000003215d524d6419214568ba42a31502f2a58a97d0139c66908e9d71755f5a7666567aafe30ea84d89308f06768f28a648",
        .name = "matter_g1_add_7",
        .gas = 375,
    },
    {
        .input = "0000000000000000000000000000000009d6424e002439998e91cd509f85751ad25e574830c564e7568347d19e3f38add0cab067c0b4b0801785a78bcbeaf246000000000000000000000000000000000ef6d7db03ee654503b46ff0dbc3297536a422e963bda9871a8da8f4eeb98dedebd6071c4880b4636198f4c2375dc795000000000000000000000000000000000d713e148769fac2efd380886f8566c6d4662dd38317bb7e68744c4339efaedbab88435ce3dc289afaa7ecb37df37a5300000000000000000000000000000000129d9cd031b31c77a4e68093dcdbb585feba786207aa115d9cf120fe4f19ca31a0dca9c692bd0f53721d60a55c333129",
        .expected = "00000000000000000000000000000000029405b9615e14bdac8b5666bbc5f3843d4bca17c97bed66d164f1b58d2a148f0f506d645d665a40e60d53fe29375ed400000000000000000000000000000000162761f1712814e474beb2289cc50519253d680699b530c2a6477f727ccc75a19681b82e490f441f91a3c611eeb0e9e2",
        .name = "matter_g1_add_8",
        .gas = 375,
    },
    {
        .input = "0000000000000000000000000000000002d1cdb93191d1f9f0308c2c55d0208a071f5520faca7c52ab0311dbc9ba563bd33b5dd6baa77bf45ac2c3269e945f4800000000000000000000000000000000072a52106e6d7b92c594c4dacd20ef5fab7141e45c231457cd7e71463b2254ee6e72689e516fa6a8f29f2a173ce0a1900000000000000000000000000000000006d92bcb599edca426ff4ceeb154ebf133c2dea210c7db0441f74bd37c8d239149c8b5056ace0bfefb1db04b42664f530000000000000000000000000000000008522fc155eef6d5746283808091f91b427f2a96ac248850f9e3d7aadd14848101c965663fd4a63aea1153d71918435a",
        .expected = "000000000000000000000000000000000cfaa8df9437c0b6f344a0c8dcbc7529a07aec0d7632ace89af6796b6b960b014f78dd10e987a993fb8a95cc909822ec0000000000000000000000000000000007475f115f6eb35f78ba9a2b71a44ccb6bbc1e980b8cd369c5c469565f3fb798bc907353cf47f524ba715deaedf379cb",
        .name = "matter_g1_add_9",
        .gas = 375,
    },
    {
        .input = "0000000000000000000000000000000000641642f6801d39a09a536f506056f72a619c50d043673d6d39aa4af11d8e3ded38b9c3bbc970dbc1bd55d68f94b50d0000000000000000000000000000000009ab050de356a24aea90007c6b319614ba2f2ed67223b972767117769e3c8e31ee4056494628fb2892d3d37afb6ac9430000000000000000000000000000000016380d03b7c5cc3301ffcb2cf7c28c9bde54fc22ba2b36ec293739d8eb674678c8e6461e34c1704747817c8f8341499a000000000000000000000000000000000ec6667aa5c6a769a64c180d277a341926376c39376480dc69fcad9a8d3b540238eb39d05aaa8e3ca15fc2c3ab696047",
        .expected = "0000000000000000000000000000000011541d798b4b5069e2541fa5410dad03fd02784332e72658c7b0fa96c586142a967addc11a7a82bfcee33bd5d07066b900000000000000000000000000000000195b3fcb94ab7beb908208283b4e5d19c0af90fca4c76268f3c703859dea7d038aca976927f48839ebc7310869c724aa",
        .name = "matter_g1_add_10",
        .gas = 375,
    },
    {
        .input = "000000000000000000000000000000000fd4893addbd58fb1bf30b8e62bef068da386edbab9541d198e8719b2de5beb9223d87387af82e8b55bd521ff3e47e2d000000000000000000000000000000000f3a923b76473d5b5a53501790cb02597bb778bdacb3805a9002b152d22241ad131d0f0d6a260739cbab2c2fe602870e00000000000000000000000000000000065eb0770ab40199658bf87db6c6b52cd8c6c843a3e40dd60433d4d79971ff31296c9e00a5d553df7c81ade533379f4b0000000000000000000000000000000017a6f6137ddd90c15cf5e415f040260e15287d8d2254c6bfee88938caec9e5a048ff34f10607d1345ba1f09f30441ef4",
        .expected = "0000000000000000000000000000000006b0853b3d41fc2d7b27da0bb2d6eb76be32530b59f8f537d227a6eb78364c7c0760447494a8bba69ef4b256dbef750200000000000000000000000000000000166e55ba2d20d94da474d4a085c14245147705e252e2a76ae696c7e37d75cde6a77fea738cef045182d5e628924dc0bb",
        .name = "matter_g1_add_11",
        .gas = 375,
    },
    {
        .input = "0000000000000000000000000000000002cb4b24c8aa799fd7cb1e4ab1aab1372113200343d8526ea7bc64dfaf926baf5d90756a40e35617854a2079cd07fba40000000000000000000000000000000003327ca22bd64ebd673cc6d5b02b2a8804d5353c9d251637c4273ad08d581cc0d58da9bea27c37a0b3f4961dbafd276b0000000000000000000000000000000006a3f7eb0e42567210cc1ba5e6f8c42d02f1eef325b6483fef49ba186f59ab69ca2284715b736086d2a0a1f0ea224b40000000000000000000000000000000000bc08427fda31a6cfbe657a8c71c73894a33700e93e411d42f1471160c403b939b535070b68d60a4dc50e47493da63dc",
        .expected = "000000000000000000000000000000000c35d4cd5d43e9cf52c15d46fef521666a1e1ab9f0b4a77b8e78882e9fab40f3f988597f202c5bd176c011a56a1887d4000000000000000000000000000000000ae2b5c24928a00c02daddf03fade45344f250dcf4c12eda06c39645b4d56147cb239d95b06fd719d4dc20fe332a6fce",
        .name = "matter_g1_add_12",
        .gas = 375,
    },
    {
        .input = "00000000000000000000000000000000024ad70f2b2105ca37112858e84c6f5e3ffd4a8b064522faae1ecba38fabd52a6274cb46b00075deb87472f11f2e67d90000000000000000000000000000000010a502c8b2a68aa30d2cb719273550b9a3c283c35b2e18a01b0b765344ffaaa5cb30a1e3e6ecd3a53ab67658a578768100000000000000000000000000000000068e79aea45b7199ec4b6f26e01e88ec76533743639ce76df66937fff9e7de3edf6700d227f10f43e073afcc63e2eddc00000000000000000000000000000000039c0b6d9e9681401aeb57a94cedc0709a0eff423ace9253eb00ae75e21cabeb626b52ef4368e6a4592aed9689c6fca4",
        .expected = "0000000000000000000000000000000013bad27dafa20f03863454c30bd5ae6b202c9c7310875da302d4693fc1c2b78cca502b1ff851b183c4b2564c5d3eb4dc0000000000000000000000000000000000552b322b3d672704382b5d8b214c225b4f7868f9c5ae0766b7cdb181f97ed90a4892235915ffbc0daf3e14ec98a606",
        .name = "matter_g1_add_13",
        .gas = 375,
    },
};

static const std::vector<test_case> BLS_G1_MUL_VALID_PRAGUE_TEST_CASES =
{
    {
        .input = "0000000000000000000000000000000017f1d3a73197d7942695638c4fa9ac0fc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bb0000000000000000000000000000000008b3f481e3aaa0f1a09e30ed741d8ae4fcf5e095d5d00af600db18cb2c04b3edd03cc744a2888ae40caa232946c5e7e10000000000000000000000000000000000000000000000000000000000000002",
        .expected = "000000000000000000000000000000000572cbea904d67468808c8eb50a9450c9721db309128012543902d0ac358a62ae28f75bb8f1c7c42c39a8c5529bf0f4e00000000000000000000000000000000166a9d8cabc673a322fda673779d8e3822ba3ecb8670e461f73bb9021d5fd76a4c56d9d4cd16bd1bba86881979749d28",
        .name = "bls_g1mul_(g1+g1=2*g1)",
        .gas =12000,
    },
    {
        .input = "00000000000000000000000000000000112b98340eee2777cc3c14163dea3ec97977ac3dc5c70da32e6e87578f44912e902ccef9efe28d4a78b8999dfbca942600000000000000000000000000000000186b28d92356c4dfec4b5201ad099dbdede3781f8998ddf929b4cd7756192185ca7b8f4ef7088f813270ac3d48868a210000000000000000000000000000000000000000000000000000000000000002",
        .expected = "0000000000000000000000000000000015222cddbabdd764c4bee0b3720322a65ff4712c86fc4b1588d0c209210a0884fa9468e855d261c483091b2bf7de6a630000000000000000000000000000000009f9edb99bc3b75d7489735c98b16ab78b9386c5f7a1f76c7e96ac6eb5bbde30dbca31a74ec6e0f0b12229eecea33c39",
        .name = "bls_g1mul_(p1+p1=2*p1)",
        .gas =12000,
    },
    {
        .input = "0000000000000000000000000000000017f1d3a73197d7942695638c4fa9ac0fc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bb0000000000000000000000000000000008b3f481e3aaa0f1a09e30ed741d8ae4fcf5e095d5d00af600db18cb2c04b3edd03cc744a2888ae40caa232946c5e7e10000000000000000000000000000000000000000000000000000000000000001",
        .expected = "0000000000000000000000000000000017f1d3a73197d7942695638c4fa9ac0fc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bb0000000000000000000000000000000008b3f481e3aaa0f1a09e30ed741d8ae4fcf5e095d5d00af600db18cb2c04b3edd03cc744a2888ae40caa232946c5e7e1",
        .name = "bls_g1mul_(1*g1=g1)",
        .gas =12000,
    },
    {
        .input = "00000000000000000000000000000000112b98340eee2777cc3c14163dea3ec97977ac3dc5c70da32e6e87578f44912e902ccef9efe28d4a78b8999dfbca942600000000000000000000000000000000186b28d92356c4dfec4b5201ad099dbdede3781f8998ddf929b4cd7756192185ca7b8f4ef7088f813270ac3d48868a210000000000000000000000000000000000000000000000000000000000000001",
        .expected = "00000000000000000000000000000000112b98340eee2777cc3c14163dea3ec97977ac3dc5c70da32e6e87578f44912e902ccef9efe28d4a78b8999dfbca942600000000000000000000000000000000186b28d92356c4dfec4b5201ad099dbdede3781f8998ddf929b4cd7756192185ca7b8f4ef7088f813270ac3d48868a21",
        .name = "bls_g1mul_(1*p1=p1)",
        .gas =12000,
    },
    {
        .input = "0000000000000000000000000000000017f1d3a73197d7942695638c4fa9ac0fc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bb0000000000000000000000000000000008b3f481e3aaa0f1a09e30ed741d8ae4fcf5e095d5d00af600db18cb2c04b3edd03cc744a2888ae40caa232946c5e7e10000000000000000000000000000000000000000000000000000000000000000",
        .expected = "0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000",
        .name = "bls_g1mul_(0*g1=inf)",
        .gas =12000,
    },
    {
        .input = "00000000000000000000000000000000112b98340eee2777cc3c14163dea3ec97977ac3dc5c70da32e6e87578f44912e902ccef9efe28d4a78b8999dfbca942600000000000000000000000000000000186b28d92356c4dfec4b5201ad099dbdede3781f8998ddf929b4cd7756192185ca7b8f4ef7088f813270ac3d48868a210000000000000000000000000000000000000000000000000000000000000000",
        .expected = "0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000",
        .name = "bls_g1mul_(0*p1=inf)",
        .gas =12000,
    },
    {
        .input = "00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000011",
        .expected = "0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000",
        .name = "bls_g1mul_(x*inf=inf)",
        .gas =12000,
    },
    {
        .input = "0000000000000000000000000000000017f1d3a73197d7942695638c4fa9ac0fc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bb0000000000000000000000000000000008b3f481e3aaa0f1a09e30ed741d8ae4fcf5e095d5d00af600db18cb2c04b3edd03cc744a2888ae40caa232946c5e7e1263dbd792f5b1be47ed85f8938c0f29586af0d3ac7b977f21c278fe1462040e3",
        .expected = "000000000000000000000000000000000491d1b0ecd9bb917989f0e74f0dea0422eac4a873e5e2644f368dffb9a6e20fd6e10c1b77654d067c0618f6e5a7f79a0000000000000000000000000000000017cd7061575d3e8034fcea62adaa1a3bc38dca4b50e4c5c01d04dd78037c9cee914e17944ea99e7ad84278e5d49f36c4",
        .name = "bls_g1mul_random*g1",
        .gas =12000,
    },
    {
        .input = "00000000000000000000000000000000112b98340eee2777cc3c14163dea3ec97977ac3dc5c70da32e6e87578f44912e902ccef9efe28d4a78b8999dfbca942600000000000000000000000000000000186b28d92356c4dfec4b5201ad099dbdede3781f8998ddf929b4cd7756192185ca7b8f4ef7088f813270ac3d48868a21263dbd792f5b1be47ed85f8938c0f29586af0d3ac7b977f21c278fe1462040e3",
        .expected = "0000000000000000000000000000000006ee9c9331228753bcb148d0ca8623447701bb0aa6eafb0340aa7f81543923474e00f2a225de65c62dd1d8303270220c0000000000000000000000000000000018dd7be47eb4e80985d7a0d2cc96c8b004250b36a5c3ec0217705d453d3ecc6d0d3d1588722da51b40728baba1e93804",
        .name = "bls_g1mul_random*p1",
        .gas =12000,
    },
    {
        .input = "0000000000000000000000000000000017f1d3a73197d7942695638c4fa9ac0fc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bb0000000000000000000000000000000008b3f481e3aaa0f1a09e30ed741d8ae4fcf5e095d5d00af600db18cb2c04b3edd03cc744a2888ae40caa232946c5e7e19a2b64cc58f8992cb21237914262ca9ada6cb13dc7b7d3f11c278fe0462040e4",
        .expected = "000000000000000000000000000000000491d1b0ecd9bb917989f0e74f0dea0422eac4a873e5e2644f368dffb9a6e20fd6e10c1b77654d067c0618f6e5a7f79a0000000000000000000000000000000017cd7061575d3e8034fcea62adaa1a3bc38dca4b50e4c5c01d04dd78037c9cee914e17944ea99e7ad84278e5d49f36c4",
        .name = "bls_g1mul_random*g1_unnormalized_scalar",
        .gas =12000,
    },
    {
        .input = "00000000000000000000000000000000112b98340eee2777cc3c14163dea3ec97977ac3dc5c70da32e6e87578f44912e902ccef9efe28d4a78b8999dfbca942600000000000000000000000000000000186b28d92356c4dfec4b5201ad099dbdede3781f8998ddf929b4cd7756192185ca7b8f4ef7088f813270ac3d48868a219a2b64cc58f8992cb21237914262ca9ada6cb13dc7b7d3f11c278fe0462040e4",
        .expected = "0000000000000000000000000000000006ee9c9331228753bcb148d0ca8623447701bb0aa6eafb0340aa7f81543923474e00f2a225de65c62dd1d8303270220c0000000000000000000000000000000018dd7be47eb4e80985d7a0d2cc96c8b004250b36a5c3ec0217705d453d3ecc6d0d3d1588722da51b40728baba1e93804",
        .name = "bls_g1mul_random*p1_unnormalized_scalar",
        .gas =12000,
    }
};

static const std::vector<test_case> BLS_G1_MSM_VALID_PRAGUE_TEST_CASES = {
    {
        .input = "0000000000000000000000000000000017f1d3a73197d7942695638c4fa9ac0fc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bb0000000000000000000000000000000008b3f481e3aaa0f1a09e30ed741d8ae4fcf5e095d5d00af600db18cb2c04b3edd03cc744a2888ae40caa232946c5e7e10000000000000000000000000000000000000000000000000000000000000011",
        .expected = "000000000000000000000000000000001098f178f84fc753a76bb63709e9be91eec3ff5f7f3a5f4836f34fe8a1a6d6c5578d8fd820573cef3a01e2bfef3eaf3a000000000000000000000000000000000ea923110b733b531006075f796cc9368f2477fe26020f465468efbb380ce1f8eebaf5c770f31d320f9bd378dc758436",
        .name = "bls_g1multiexp_single",
        .gas = 12000,
    },
    {
        .input = "0000000000000000000000000000000017f1d3a73197d7942695638c4fa9ac0fc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bb0000000000000000000000000000000008b3f481e3aaa0f1a09e30ed741d8ae4fcf5e095d5d00af600db18cb2c04b3edd03cc744a2888ae40caa232946c5e7e10000000000000000000000000000000000000000000000000000000000000032000000000000000000000000000000000e12039459c60491672b6a6282355d8765ba6272387fb91a3e9604fa2a81450cf16b870bb446fc3a3e0a187fff6f89450000000000000000000000000000000018b6c1ed9f45d3cbc0b01b9d038dcecacbd702eb26469a0eb3905bd421461712f67f782b4735849644c1772c93fe3d09000000000000000000000000000000000000000000000000000000000000003300000000000000000000000000000000147b327c8a15b39634a426af70c062b50632a744eddd41b5a4686414ef4cd9746bb11d0a53c6c2ff21bbcf331e07ac9200000000000000000000000000000000078c2e9782fa5d9ab4e728684382717aa2b8fad61b5f5e7cf3baa0bc9465f57342bb7c6d7b232e70eebcdbf70f903a450000000000000000000000000000000000000000000000000000000000000034",
        .expected = "000000000000000000000000000000001339b4f51923efe38905f590ba2031a2e7154f0adb34a498dfde8fb0f1ccf6862ae5e3070967056385055a666f1b6fc70000000000000000000000000000000009fb423f7e7850ef9c4c11a119bb7161fe1d11ac5527051b29fe8f73ad4262c84c37b0f1b9f0e163a9682c22c7f98c80",
        .name = "bls_g1multiexp_multiple",
        .gas = 30528,
    },
    {
        .input = "0000000000000000000000000000000017f1d3a73197d7942695638c4fa9ac0fc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bb0000000000000000000000000000000008b3f481e3aaa0f1a09e30ed741d8ae4fcf5e095d5d00af600db18cb2c04b3edd03cc744a2888ae40caa232946c5e7e1000000000000000000000000000000000000000000000000000000000000005b000000000000000000000000000000000572cbea904d67468808c8eb50a9450c9721db309128012543902d0ac358a62ae28f75bb8f1c7c42c39a8c5529bf0f4e00000000000000000000000000000000166a9d8cabc673a322fda673779d8e3822ba3ecb8670e461f73bb9021d5fd76a4c56d9d4cd16bd1bba86881979749d2800000000000000000000000000000000000000000000000000000000000020590000000000000000000000000000000009ece308f9d1f0131765212deca99697b112d61f9be9a5f1f3780a51335b3ff981747a0b2ca2179b96d2c0c9024e522400000000000000000000000000000000032b80d3a6f5b09f8a84623389c5f80ca69a0cddabc3097f9d9c27310fd43be6e745256c634af45ca3473b0590ae30d100000000000000000000000000000000000000000000000000000000000b7fa3000000000000000000000000000000000c9b60d5afcbd5663a8a44b7c5a02f19e9a77ab0a35bd65809bb5c67ec582c897feb04decc694b13e08587f3ff9b5b6000000000000000000000000000000000143be6d078c2b79a7d4f1d1b21486a030ec93f56aa54e1de880db5a66dd833a652a95bee27c824084006cb5644cbd43f0000000000000000000000000000000000000000000000000000000004165ef10000000000000000000000000000000010e7791fb972fe014159aa33a98622da3cdc98ff707965e536d8636b5fcc5ac7a91a8c46e59a00dca575af0f18fb13dc0000000000000000000000000000000016ba437edcc6551e30c10512367494bfb6b01cc6681e8a4c3cd2501832ab5c4abc40b4578b85cbaffbf0bcd70d67c6e20000000000000000000000000000000000000000000000000000000173f3bfab0000000000000000000000000000000006e82f6da4520f85c5d27d8f329eccfa05944fd1096b20734c894966d12a9e2a9a9744529d7212d33883113a0cadb9090000000000000000000000000000000017d81038f7d60bee9110d9c0d6d1102fe2d998c957f28e31ec284cc04134df8e47e8f82ff3af2e60a6d9688a4563477c0000000000000000000000000000000000000000000000000000008437a521c9000000000000000000000000000000001928f3beb93519eecf0145da903b40a4c97dca00b21f12ac0df3be9116ef2ef27b2ae6bcd4c5bc2d54ef5a70627efcb700000000000000000000000000000000108dadbaa4b636445639d5ae3089b3c43a8a1d47818edd1839d7383959a41c10fdc66849cfa1b08c5a11ec7e28981a1c00000000000000000000000000000000000000000000000000002effc7b3027300000000000000000000000000000000085ae765588126f5e860d019c0e26235f567a9c0c0b2d8ff30f3e8d436b1082596e5e7462d20f5be3764fd473e57f9cf0000000000000000000000000000000019e7dfab8a794b6abb9f84e57739de172a63415273f460d1607fa6a74f0acd97d9671b801dd1fd4f18232dd1259359a10000000000000000000000000000000000000000000000000010b4ebfca1dee10000000000000000000000000000000019cdf3807146e68e041314ca93e1fee0991224ec2a74beb2866816fd0826ce7b6263ee31e953a86d1b72cc2215a577930000000000000000000000000000000007481b1f261aabacf45c6e4fc278055441bfaf99f604d1f835c0752ac9742b4522c9f5c77db40989e7da608505d4861600000000000000000000000000000000000000000000000005f04fe2cd8a39fb000000000000000000000000000000000f81da25ecf1c84b577fefbedd61077a81dc43b00304015b2b596ab67f00e41c86bb00ebd0f90d4b125eb0539891aeed0000000000000000000000000000000011af629591ec86916d6ce37877b743fe209a3af61147996c1df7fd1c47b03181cd806fd31c3071b739e4deb234bd9e190000000000000000000000000000000000000000000000021c6c659f10229c390000000000000000000000000000000000fd75ebcc0a21649e3177bcce15426da0e4f25d6828fbf4038d4d7ed3bd4421de3ef61d70f794687b12b2d571971a550000000000000000000000000000000004523f5a3915fc57ee889cdb057e3e76109112d125217546ccfe26810c99b130d1b27820595ad61c7527dc5bbb132a900000000000000000000000000000000000000000000000c01a881f8abc4d8843000000000000000000000000000000000345dd80ffef0eaec8920e39ebb7f5e9ae9c1d6179e9129b705923df7830c67f3690cbc48649d4079eadf5397339580c00000000000000000000000000000000083d3baf25e42f2845d8fa594dda2e0f40a4d670dda40f30da0aff0d81c87ac3d687fe84eca72f34c7c755a045668cf10000000000000000000000000000000000000000000044496e633650ef8f6fd100000000000000000000000000000000051f8a0b82a6d86202a61cbc3b0f3db7d19650b914587bde4715ccd372e1e40cab95517779d840416e1679c84a6db24e000000000000000000000000000000000b6a63ac48b7d7666ccfcf1e7de0097c5e6e1aacd03507d23fb975d8daec42857b3a471bf3fc471425b63864e045f4df00000000000000000000000000000000000000000018461a3d444ec527fcbf4b0000000000000000000000000000000019bef05aaba1ea467fcbc9c420f5e3153c9d2b5f9bf2c7e2e7f6946f854043627b45b008607b9a9108bb96f3c1c089d3000000000000000000000000000000000adb3250ba142db6a748a85e4e401fa0490dd10f27068d161bd47cb562cc189b3194ab53a998e48a48c65e071bb54117000000000000000000000000000000000000000008a0eb53c748001536d7ffa9000000000000000000000000000000000d9e19b3f4c7c233a6112e5397309f9812a4f61f754f11dd3dcb8b07d55a7b1dfea65f19a1488a14fef9a414950835820000000000000000000000000000000009d0d1f706f1a85a98f3efaf5c35a41c9182afc129285cf2db3212f6ea0da586ca539bc66181f2ccb228485dd8aff0a700000000000000000000000000000000000000031133a6c7d698078a7ec7e11300000000000000000000000000000000073eb991aa22cdb794da6fcde55a427f0a4df5a4a70de23a988b5e5fc8c4d844f66d990273267a54dd21579b7ba6a086000000000000000000000000000000001825bacd18f695351f843521ebeada20352c3c3965626f98bc4c68e6ff7c4eed38b48f328204bbb9cd461511d24ebfb300000000000000000000000000000000000001171d5c4909480aae3b110d01c1000000000000000000000000000000001098f178f84fc753a76bb63709e9be91eec3ff5f7f3a5f4836f34fe8a1a6d6c5578d8fd820573cef3a01e2bfef3eaf3a000000000000000000000000000000000ea923110b733b531006075f796cc9368f2477fe26020f465468efbb380ce1f8eebaf5c770f31d320f9bd378dc75843600000000000000000000000000000000000063376fcdf64c9bcbeeff0f9f9f9b000000000000000000000000000000001252a4ac3529f8b2b6e8189b95a60b8865f07f9a9b73f98d5df708511d3f68632c4c7d1e2b03e6b1d1e2c01839752ada0000000000000000000000000000000002a1bc189e36902d1a49b9965eca3cb818ab5c26dffca63ca9af032870f7bbc615ac65f21bed27bd77dd65f2e90f535800000000000000000000000000000000002344b4be368d3b617df4aa8dbdbc19000000000000000000000000000000001271205227c7aa27f45f20b3ba380dfea8b51efae91fd32e552774c99e2a1237aa59c0c43f52aad99bba3783ea2f36a4000000000000000000000000000000001407ffc2c1a2fe3b00d1f91e1f4febcda31004f7c301075c9031c55dd3dfa8104b156a6a3b7017fccd27f81c2af222ef000000000000000000000000000000000c896c3f9d64341ba7c5f8a06271dce3000000000000000000000000000000000272e9d1d50a4aea7d8f0583948090d0888be5777f2846800b8281139cd4aa9eee05f89b069857a3e77ccfaae1615f9c0000000000000000000000000000000016ab25d6a997bcac8999d481633caa41606894aae9770cdb54aac65ac0a454dd0346b3428fefd837b1e3f654f8217f4a0000000000000000000000000000000474d97a9cf29e85d4a35f6102fe7984b1000000000000000000000000000000001780e853f8ce7eda772c6691d25e220ca1d2ab0db51a7824b700620f7ac94c06639e91c98bb6abd78128f0ec845df8ef00000000000000000000000000000000095bc13d5a05c686e20d7b904db4931272d84d051a516fbb23acf7981d39bffa3943d08a9be01fc48e5241cd8b775ddd00000000000000000000000000000195894e95ca3e59929612e77c1075322aeb000000000000000000000000000000000b48aa2cc6f4a0bb63b5d67be54ac3aed10326dda304c5aeb9e942b40d6e7610478377680ab90e092ef1895e62786008000000000000000000000000000000000f6fc00c0697119a34363c0294acf608eca3c680d80183a59c89b45a66dc750f818a27e3a6e136d69e7580a8afca001b00000000000000000000000000009027ceef3ee429d71b58b84919d9a8d54189000000000000000000000000000000000c8b694b04d98a749a0763c72fc020ef61b2bb3f63ebb182cb2e568f6a8b9ca3ae013ae78317599e7e7ba2a528ec754a000000000000000000000000000000000951b70c206350e1edc2aefdfaa95318368c151e01e468b9fb1cf7c3c6575e4f06c135715cc5e51e1b492d19adf9bee000000000000000000000000000333e268f0b5b1adf76b88981fc305f03ce4bb3000000000000000000000000000000001717182463fbe215168e6762abcbb55c5c65290f2b5a2af616f8a6f50d625b46164178a11622d21913efdfa4b800648d0000000000000000000000000000000008531aa42aa092a91e0894d84ff0bcec0d37cede43dec85cca80ffad335d6f69da18335869ba1174f73bb37501404d6f000000000000000000000000123717b4d909628d6f3398e134a531c65a54e8a1000000000000000000000000000000000cb58c81ae0cae2e9d4d446b730922239923c345744eee58efaadb36e9a0925545b18a987acf0bad469035b291e37269000000000000000000000000000000001678cefdd942f60480b5f69738a6a4cea5e1a9239d1bd5f701ad96c2dd1fd252f0aeea219bddcda4bc8f83983a282aff00000000000000000000000679956d49265608468757580db6b8b1821c2eb13b",
        .expected = "0000000000000000000000000000000005548dad0613ef8804a347152e8267acdbbcab98a795fc0da2d9df5c8ec37e0eb32e82950fbe5f8ec330b8bffafe13e40000000000000000000000000000000014e94dbbf60d89b3f68a5a076fcbd7cc0b683eae228f5d5036ee61012996ae2d347cec19dbd4eab547fadecdb31c078a",
        .name = "bls_g1multiexp_larger",
        .gas = 193500,
    },
};

static const std::vector<test_case> BLS_MAP_G1_VALID_PRAGUE_TEST_CASES = {
    {
        .input = "0000000000000000000000000000000014406e5bfb9209256a3820879a29ac2f62d6aca82324bf3ae2aa7d3c54792043bd8c791fccdb080c1a52dc68b8b69350",
        .expected = "000000000000000000000000000000000d7721bcdb7ce1047557776eb2659a444166dc6dd55c7ca6e240e21ae9aa18f529f04ac31d861b54faf3307692545db700000000000000000000000000000000108286acbdf4384f67659a8abe89e712a504cb3ce1cba07a716869025d60d499a00d1da8cdc92958918c222ea93d87f0",
        .name = "matter_fp_to_g1_0",
        .gas = 5500,
    },
    {
        .input = "000000000000000000000000000000000e885bb33996e12f07da69073e2c0cc880bc8eff26d2a724299eb12d54f4bcf26f4748bb020e80a7e3794a7b0e47a641",
        .expected = "00000000000000000000000000000000191ba6e4c4dafa22c03d41b050fe8782629337641be21e0397dc2553eb8588318a21d30647182782dee7f62a22fd020c000000000000000000000000000000000a721510a67277eabed3f153bd91df0074e1cbd37ef65b85226b1ce4fb5346d943cf21c388f0c5edbc753888254c760a",
        .name = "matter_fp_to_g1_1",
        .gas = 5500,
    },
    {
        .input = "000000000000000000000000000000000ba1b6d79150bdc368a14157ebfe8b5f691cf657a6bbe30e79b6654691136577d2ef1b36bfb232e3336e7e4c9352a8ed",
        .expected = "000000000000000000000000000000001658c31c0db44b5f029dba56786776358f184341458577b94d3a53c877af84ffbb1a13cc47d228a76abb4b67912991850000000000000000000000000000000018cf1f27eab0a1a66f28a227bd624b7d1286af8f85562c3f03950879dd3b8b4b72e74b034223c6fd93de7cd1ade367cb",
        .name = "matter_fp_to_g1_2",
        .gas = 5500,
    },
    {
        .input = "000000000000000000000000000000000f12847f7787f439575031bcdb1f03cfb79f942f3a9709306e4bd5afc73d3f78fd1c1fef913f503c8cbab58453fb7df2",
        .expected = "000000000000000000000000000000001672a8831d3e8bf9441972969e56b338594c5c0ede7bdba5b4113ac31ccb848dc2a2c4e23c0b9ec88bfe7165f472b427000000000000000000000000000000000a86e65037cccb5281389512673068d6f91606923629905e895f630059cf87fb37e716494db288958316c6a50de65ca1",
        .name = "matter_fp_to_g1_3",
        .gas = 5500,
    },
};

TEST(Prague, blsg1add_valid)
{
    do_geth_tests<EVMC_PRAGUE>(
        "bls_g1_add_valid", BLS_G1_ADD_VALID_PRAGUE_TEST_CASES, 0x0b_address);
}

TEST(Prague, blsg1mul_valid)
{
    do_geth_tests<EVMC_PRAGUE>(
        "bls_g1_mul_valid", BLS_G1_MUL_VALID_PRAGUE_TEST_CASES, 0x0c_address);
}

TEST(Prague, blsg1msm_valid)
{
    do_geth_tests<EVMC_PRAGUE>(
        "bls_g1_msm_valid", BLS_G1_MSM_VALID_PRAGUE_TEST_CASES, 0x0c_address);
}

TEST(Prague, bls_map_g1_valid)
{
    do_geth_tests<EVMC_PRAGUE>(
        "bls12_map_fp_to_g1_valid", BLS_MAP_G1_VALID_PRAGUE_TEST_CASES, 0x10_address);
}

static const std::vector<test_case> BLS_G2_ADD_VALID_PRAGUE_TEST_CASES = {
    {
        .input = "000000000000000000000000000000001638533957d540a9d2370f17cc7ed5863bc0b995b8825e0ee1ea1e1e4d00dbae81f14b0bf3611b78c952aacab827a053000000000000000000000000000000000a4edef9c1ed7f729f520e47730a124fd70662a904ba1074728114d1031e1572c6c886f6b57ec72a6178288c47c33577000000000000000000000000000000000468fb440d82b0630aeb8dca2b5256789a66da69bf91009cbfe6bd221e47aa8ae88dece9764bf3bd999d95d71e4c9899000000000000000000000000000000000f6d4552fa65dd2638b361543f887136a43253d9c66c411697003f7a13c308f5422e1aa0a59c8967acdefd8b6e36ccf300000000000000000000000000000000122915c824a0857e2ee414a3dccb23ae691ae54329781315a0c75df1c04d6d7a50a030fc866f09d516020ef82324afae0000000000000000000000000000000009380275bbc8e5dcea7dc4dd7e0550ff2ac480905396eda55062650f8d251c96eb480673937cc6d9d6a44aaa56ca66dc000000000000000000000000000000000b21da7955969e61010c7a1abc1a6f0136961d1e3b20b1a7326ac738fef5c721479dfd948b52fdf2455e44813ecfd8920000000000000000000000000000000008f239ba329b3967fe48d718a36cfe5f62a7e42e0bf1c1ed714150a166bfbd6bcf6b3b58b975b9edea56d53f23a0e849",
        .expected = "000000000000000000000000000000000411a5de6730ffece671a9f21d65028cc0f1102378de124562cb1ff49db6f004fcd14d683024b0548eff3d1468df26880000000000000000000000000000000000fb837804dba8213329db46608b6c121d973363c1234a86dd183baff112709cf97096c5e9a1a770ee9d7dc641a894d60000000000000000000000000000000019b5e8f5d4a72f2b75811ac084a7f814317360bac52f6aab15eed416b4ef9938e0bdc4865cc2c4d0fd947e7c6925fd1400000000000000000000000000000000093567b4228be17ee62d11a254edd041ee4b953bffb8b8c7f925bd6662b4298bac2822b446f5b5de3b893e1be5aa4986",
        .name = "bls_g2add_(2*g2+3*g2=5*g2)",
        .gas = 600,
    },
    {
        .input = "00000000000000000000000000000000024aa2b2f08f0a91260805272dc51051c6e47ad4fa403b02b4510b647ae3d1770bac0326a805bbefd48056c8c121bdb80000000000000000000000000000000013e02b6052719f607dacd3a088274f65596bd0d09920b61ab5da61bbdc7f5049334cf11213945d57e5ac7d055d042b7e000000000000000000000000000000000ce5d527727d6e118cc9cdc6da2e351aadfd9baa8cbdd3a76d429a695160d12c923ac9cc3baca289e193548608b82801000000000000000000000000000000000606c4a02ea734cc32acd2b02bc28b99cb3e287e85a763af267492ab572e99ab3f370d275cec1da1aaa9075ff05f79be00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000",
        .expected = "00000000000000000000000000000000024aa2b2f08f0a91260805272dc51051c6e47ad4fa403b02b4510b647ae3d1770bac0326a805bbefd48056c8c121bdb80000000000000000000000000000000013e02b6052719f607dacd3a088274f65596bd0d09920b61ab5da61bbdc7f5049334cf11213945d57e5ac7d055d042b7e000000000000000000000000000000000ce5d527727d6e118cc9cdc6da2e351aadfd9baa8cbdd3a76d429a695160d12c923ac9cc3baca289e193548608b82801000000000000000000000000000000000606c4a02ea734cc32acd2b02bc28b99cb3e287e85a763af267492ab572e99ab3f370d275cec1da1aaa9075ff05f79be",
        .name = "bls_g2add_(inf+g2=g2)",
        .gas = 600,
    },
    {
        .input = "0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000",
        .expected = "00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000",
        .name = "bls_g2add_(inf+inf=inf)",
        .gas = 600,
    },
    {
        .input = "00000000000000000000000000000000039b10ccd664da6f273ea134bb55ee48f09ba585a7e2bb95b5aec610631ac49810d5d616f67ba0147e6d1be476ea220e0000000000000000000000000000000000fbcdff4e48e07d1f73ec42fe7eb026f5c30407cfd2f22bbbfe5b2a09e8a7bb4884178cb6afd1c95f80e646929d30040000000000000000000000000000000001ed3b0e71acb0adbf44643374edbf4405af87cfc0507db7e8978889c6c3afbe9754d1182e98ac3060d64994d31ef576000000000000000000000000000000001681a2bf65b83be5a2ca50430949b6e2a099977482e9405b593f34d2ed877a3f0d1bddc37d0cec4d59d7df74b2b8f2df0000000000000000000000000000000017c9fcf0504e62d3553b2f089b64574150aa5117bd3d2e89a8c1ed59bb7f70fb83215975ef31976e757abf60a75a1d9f0000000000000000000000000000000008f5a53d704298fe0cfc955e020442874fe87d5c729c7126abbdcbed355eef6c8f07277bee6d49d56c4ebaf334848624000000000000000000000000000000001302dcc50c6ce4c28086f8e1b43f9f65543cf598be440123816765ab6bc93f62bceda80045fbcad8598d4f32d03ee8fa000000000000000000000000000000000bbb4eb37628d60b035a3e0c45c0ea8c4abef5a6ddc5625e0560097ef9caab208221062e81cd77ef72162923a1906a40",
        .expected = "000000000000000000000000000000000a9b880c2c13da05bdeda62ea8f61e5fc2bf0b7aa5cc31eaf512bef7c5073d9e9927084b512e818dbf05eab697ba0661000000000000000000000000000000000b963b527aa3ec36813b108f2294115f732c878ac28551b5490615b436406773b5bb6a3f002be0e54db0bcebe40cb2e2000000000000000000000000000000000bd6e9060b42e36b57d88bc95b8b993da2d9d5acd95b73bad0509c2324212bcf7a94a46901932c0750535d00008a34f7000000000000000000000000000000000a374afd32bc3bb20c22a8864ce0dafe298bda17260b9d1d598a80830400c3fd4e8a8f677630eae5d4aa0a76a434e0ba",
        .name = "matter_g2_add_0",
        .gas = 600,
    },
    {
        .input = "0000000000000000000000000000000018c0ada6351b70661f053365deae56910798bd2ace6e2bf6ba4192d1a229967f6af6ca1c9a8a11ebc0a232344ee0f6d6000000000000000000000000000000000cc70a587f4652039d8117b6103858adcd9728f6aebe230578389a62da0042b7623b1c0436734f463cfdd187d20903240000000000000000000000000000000009f50bd7beedb23328818f9ffdafdb6da6a4dd80c5a9048ab8b154df3cad938ccede829f1156f769d9e149791e8e0cd900000000000000000000000000000000079ba50d2511631b20b6d6f3841e616e9d11b68ec3368cd60129d9d4787ab56c4e9145a38927e51c9cd6271d493d938800000000000000000000000000000000192fa5d8732ff9f38e0b1cf12eadfd2608f0c7a39aced7746837833ae253bb57ef9c0d98a4b69eeb2950901917e99d1e0000000000000000000000000000000009aeb10c372b5ef1010675c6a4762fda33636489c23b581c75220589afbc0cc46249f921eea02dd1b761e036ffdbae220000000000000000000000000000000002d225447600d49f932b9dd3ca1e6959697aa603e74d8666681a2dca8160c3857668ae074440366619eb8920256c4e4a00000000000000000000000000000000174882cdd3551e0ce6178861ff83e195fecbcffd53a67b6f10b4431e423e28a480327febe70276036f60bb9c99cf7633",
        .expected = "000000000000000000000000000000001963e94d1501b6038de347037236c18a0a0c8cec677e48fc514e9fc9753a7d8dcf0acc4b3b64572cb571aebbe0b696640000000000000000000000000000000000d9739acc3a60f6dffb26f9b5f1fd114a21f2983deea192663c53e012b9f8e1cabd4942ad039badbd4745ddc0a26a91000000000000000000000000000000000b4206dcdb80d62195febb6773acab25fa2c09a2e4be9416ca019faeb72f1fad1dfdc51e8cea39b371a045b18947d40a00000000000000000000000000000000100758b888fa27e9258ddd5d83409e8aeac576874bc399b33b8bc50d77fce5358cb091d42f9a1b1ed09be3f200959989",
        .name = "matter_g2_add_1",
        .gas = 600,
    },
};

static const std::vector<test_case> BLS_G2_MUL_VALID_PRAGUE_TEST_CASES = {
    {
        .input = "00000000000000000000000000000000024aa2b2f08f0a91260805272dc51051c6e47ad4fa403b02b4510b647ae3d1770bac0326a805bbefd48056c8c121bdb80000000000000000000000000000000013e02b6052719f607dacd3a088274f65596bd0d09920b61ab5da61bbdc7f5049334cf11213945d57e5ac7d055d042b7e000000000000000000000000000000000ce5d527727d6e118cc9cdc6da2e351aadfd9baa8cbdd3a76d429a695160d12c923ac9cc3baca289e193548608b82801000000000000000000000000000000000606c4a02ea734cc32acd2b02bc28b99cb3e287e85a763af267492ab572e99ab3f370d275cec1da1aaa9075ff05f79be0000000000000000000000000000000000000000000000000000000000000002",
        .expected = "000000000000000000000000000000001638533957d540a9d2370f17cc7ed5863bc0b995b8825e0ee1ea1e1e4d00dbae81f14b0bf3611b78c952aacab827a053000000000000000000000000000000000a4edef9c1ed7f729f520e47730a124fd70662a904ba1074728114d1031e1572c6c886f6b57ec72a6178288c47c33577000000000000000000000000000000000468fb440d82b0630aeb8dca2b5256789a66da69bf91009cbfe6bd221e47aa8ae88dece9764bf3bd999d95d71e4c9899000000000000000000000000000000000f6d4552fa65dd2638b361543f887136a43253d9c66c411697003f7a13c308f5422e1aa0a59c8967acdefd8b6e36ccf3",
        .name = "bls_g2mul_(g2+g2=2*g2)",
        .gas = 22500,
    },
    {
        .input = "00000000000000000000000000000000103121a2ceaae586d240843a398967325f8eb5a93e8fea99b62b9f88d8556c80dd726a4b30e84a36eeabaf3592937f2700000000000000000000000000000000086b990f3da2aeac0a36143b7d7c824428215140db1bb859338764cb58458f081d92664f9053b50b3fbd2e4723121b68000000000000000000000000000000000f9e7ba9a86a8f7624aa2b42dcc8772e1af4ae115685e60abc2c9b90242167acef3d0be4050bf935eed7c3b6fc7ba77e000000000000000000000000000000000d22c3652d0dc6f0fc9316e14268477c2049ef772e852108d269d9c38dba1d4802e8dae479818184c08f9a569d8784510000000000000000000000000000000000000000000000000000000000000002",
        .expected = "000000000000000000000000000000000b76fcbb604082a4f2d19858a7befd6053fa181c5119a612dfec83832537f644e02454f2b70d40985ebb08042d1620d40000000000000000000000000000000019a4a02c0ae51365d964c73be7babb719db1c69e0ddbf9a8a335b5bed3b0a4b070d2d5df01d2da4a3f1e56aae2ec106d000000000000000000000000000000000d18322f821ac72d3ca92f92b000483cf5b7d9e5d06873a44071c4e7e81efd904f210208fe0b9b4824f01c65bc7e62080000000000000000000000000000000004e563d53609a2d1e216aaaee5fbc14ef460160db8d1fdc5e1bd4e8b54cd2f39abf6f925969fa405efb9e700b01c7085",
        .name = "bls_g2mul_(p2+p2=2*p2)",
        .gas = 22500,
    },
    {
        .input = "00000000000000000000000000000000024aa2b2f08f0a91260805272dc51051c6e47ad4fa403b02b4510b647ae3d1770bac0326a805bbefd48056c8c121bdb80000000000000000000000000000000013e02b6052719f607dacd3a088274f65596bd0d09920b61ab5da61bbdc7f5049334cf11213945d57e5ac7d055d042b7e000000000000000000000000000000000ce5d527727d6e118cc9cdc6da2e351aadfd9baa8cbdd3a76d429a695160d12c923ac9cc3baca289e193548608b82801000000000000000000000000000000000606c4a02ea734cc32acd2b02bc28b99cb3e287e85a763af267492ab572e99ab3f370d275cec1da1aaa9075ff05f79be0000000000000000000000000000000000000000000000000000000000000001",
        .expected = "00000000000000000000000000000000024aa2b2f08f0a91260805272dc51051c6e47ad4fa403b02b4510b647ae3d1770bac0326a805bbefd48056c8c121bdb80000000000000000000000000000000013e02b6052719f607dacd3a088274f65596bd0d09920b61ab5da61bbdc7f5049334cf11213945d57e5ac7d055d042b7e000000000000000000000000000000000ce5d527727d6e118cc9cdc6da2e351aadfd9baa8cbdd3a76d429a695160d12c923ac9cc3baca289e193548608b82801000000000000000000000000000000000606c4a02ea734cc32acd2b02bc28b99cb3e287e85a763af267492ab572e99ab3f370d275cec1da1aaa9075ff05f79be",
        .name = "bls_g2mul_(1*g2=g2)",
        .gas = 22500,
    },
    {
        .input = "00000000000000000000000000000000103121a2ceaae586d240843a398967325f8eb5a93e8fea99b62b9f88d8556c80dd726a4b30e84a36eeabaf3592937f2700000000000000000000000000000000086b990f3da2aeac0a36143b7d7c824428215140db1bb859338764cb58458f081d92664f9053b50b3fbd2e4723121b68000000000000000000000000000000000f9e7ba9a86a8f7624aa2b42dcc8772e1af4ae115685e60abc2c9b90242167acef3d0be4050bf935eed7c3b6fc7ba77e000000000000000000000000000000000d22c3652d0dc6f0fc9316e14268477c2049ef772e852108d269d9c38dba1d4802e8dae479818184c08f9a569d8784510000000000000000000000000000000000000000000000000000000000000001",
        .expected = "00000000000000000000000000000000103121a2ceaae586d240843a398967325f8eb5a93e8fea99b62b9f88d8556c80dd726a4b30e84a36eeabaf3592937f2700000000000000000000000000000000086b990f3da2aeac0a36143b7d7c824428215140db1bb859338764cb58458f081d92664f9053b50b3fbd2e4723121b68000000000000000000000000000000000f9e7ba9a86a8f7624aa2b42dcc8772e1af4ae115685e60abc2c9b90242167acef3d0be4050bf935eed7c3b6fc7ba77e000000000000000000000000000000000d22c3652d0dc6f0fc9316e14268477c2049ef772e852108d269d9c38dba1d4802e8dae479818184c08f9a569d878451",
        .name = "bls_g2mul_(1*p2=p2)",
        .gas = 22500,
    },
    {
        .input = "00000000000000000000000000000000024aa2b2f08f0a91260805272dc51051c6e47ad4fa403b02b4510b647ae3d1770bac0326a805bbefd48056c8c121bdb80000000000000000000000000000000013e02b6052719f607dacd3a088274f65596bd0d09920b61ab5da61bbdc7f5049334cf11213945d57e5ac7d055d042b7e000000000000000000000000000000000ce5d527727d6e118cc9cdc6da2e351aadfd9baa8cbdd3a76d429a695160d12c923ac9cc3baca289e193548608b82801000000000000000000000000000000000606c4a02ea734cc32acd2b02bc28b99cb3e287e85a763af267492ab572e99ab3f370d275cec1da1aaa9075ff05f79be0000000000000000000000000000000000000000000000000000000000000000",
        .expected = "00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000",
        .name = "bls_g2mul_(0*g2=inf)",
        .gas = 22500,
    },
    {
        .input = "00000000000000000000000000000000103121a2ceaae586d240843a398967325f8eb5a93e8fea99b62b9f88d8556c80dd726a4b30e84a36eeabaf3592937f2700000000000000000000000000000000086b990f3da2aeac0a36143b7d7c824428215140db1bb859338764cb58458f081d92664f9053b50b3fbd2e4723121b68000000000000000000000000000000000f9e7ba9a86a8f7624aa2b42dcc8772e1af4ae115685e60abc2c9b90242167acef3d0be4050bf935eed7c3b6fc7ba77e000000000000000000000000000000000d22c3652d0dc6f0fc9316e14268477c2049ef772e852108d269d9c38dba1d4802e8dae479818184c08f9a569d8784510000000000000000000000000000000000000000000000000000000000000000",
        .expected = "00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000",
        .name = "bls_g2mul_(0*p2=inf)",
        .gas = 22500,
    },
    {
        .input = "000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000011",
        .expected = "00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000",
        .name = "bls_g2mul_(x*inf=inf)",
        .gas = 22500,
    },
    {
        .input = "00000000000000000000000000000000024aa2b2f08f0a91260805272dc51051c6e47ad4fa403b02b4510b647ae3d1770bac0326a805bbefd48056c8c121bdb80000000000000000000000000000000013e02b6052719f607dacd3a088274f65596bd0d09920b61ab5da61bbdc7f5049334cf11213945d57e5ac7d055d042b7e000000000000000000000000000000000ce5d527727d6e118cc9cdc6da2e351aadfd9baa8cbdd3a76d429a695160d12c923ac9cc3baca289e193548608b82801000000000000000000000000000000000606c4a02ea734cc32acd2b02bc28b99cb3e287e85a763af267492ab572e99ab3f370d275cec1da1aaa9075ff05f79be263dbd792f5b1be47ed85f8938c0f29586af0d3ac7b977f21c278fe1462040e3",
        .expected = "0000000000000000000000000000000014856c22d8cdb2967c720e963eedc999e738373b14172f06fc915769d3cc5ab7ae0a1b9c38f48b5585fb09d4bd2733bb000000000000000000000000000000000c400b70f6f8cd35648f5c126cce5417f3be4d8eefbd42ceb4286a14df7e03135313fe5845e3a575faab3e8b949d248800000000000000000000000000000000149a0aacc34beba2beb2f2a19a440166e76e373194714f108e4ab1c3fd331e80f4e73e6b9ea65fe3ec96d7136de81544000000000000000000000000000000000e4622fef26bdb9b1e8ef6591a7cc99f5b73164500c1ee224b6a761e676b8799b09a3fd4fa7e242645cc1a34708285e4",
        .name = "bls_g2mul_random*g2",
        .gas = 22500,
    },
    {
        .input = "00000000000000000000000000000000103121a2ceaae586d240843a398967325f8eb5a93e8fea99b62b9f88d8556c80dd726a4b30e84a36eeabaf3592937f2700000000000000000000000000000000086b990f3da2aeac0a36143b7d7c824428215140db1bb859338764cb58458f081d92664f9053b50b3fbd2e4723121b68000000000000000000000000000000000f9e7ba9a86a8f7624aa2b42dcc8772e1af4ae115685e60abc2c9b90242167acef3d0be4050bf935eed7c3b6fc7ba77e000000000000000000000000000000000d22c3652d0dc6f0fc9316e14268477c2049ef772e852108d269d9c38dba1d4802e8dae479818184c08f9a569d878451263dbd792f5b1be47ed85f8938c0f29586af0d3ac7b977f21c278fe1462040e3",
        .expected = "00000000000000000000000000000000036074dcbbd0e987531bfe0e45ddfbe09fd015665990ee0c352e8e403fe6af971d8f42141970d9ab14b4dd04874409e600000000000000000000000000000000019705637f24ba2f398f32c3a3e20d6a1cd0fd63e6f8f071cf603a8334f255744927e7bfdfdb18519e019c49ff6e914500000000000000000000000000000000008e74fcff4c4278c9accfb60809ed69bbcbe3d6213ef2304e078d15ec7d6decb4f462b24b8e7cc38cc11b6f2c9e0486000000000000000000000000000000001331d40100f38c1070afd832445881b47cf4d63894666d9907c85ac66604aab5ad329980938cc3c167ccc5b6bc1b8f30",
        .name = "bls_g2mul_random*p2",
        .gas = 22500,
    },
    {
        .input = "00000000000000000000000000000000024aa2b2f08f0a91260805272dc51051c6e47ad4fa403b02b4510b647ae3d1770bac0326a805bbefd48056c8c121bdb80000000000000000000000000000000013e02b6052719f607dacd3a088274f65596bd0d09920b61ab5da61bbdc7f5049334cf11213945d57e5ac7d055d042b7e000000000000000000000000000000000ce5d527727d6e118cc9cdc6da2e351aadfd9baa8cbdd3a76d429a695160d12c923ac9cc3baca289e193548608b82801000000000000000000000000000000000606c4a02ea734cc32acd2b02bc28b99cb3e287e85a763af267492ab572e99ab3f370d275cec1da1aaa9075ff05f79be9a2b64cc58f8992cb21237914262ca9ada6cb13dc7b7d3f11c278fe0462040e4",
        .expected = "0000000000000000000000000000000014856c22d8cdb2967c720e963eedc999e738373b14172f06fc915769d3cc5ab7ae0a1b9c38f48b5585fb09d4bd2733bb000000000000000000000000000000000c400b70f6f8cd35648f5c126cce5417f3be4d8eefbd42ceb4286a14df7e03135313fe5845e3a575faab3e8b949d248800000000000000000000000000000000149a0aacc34beba2beb2f2a19a440166e76e373194714f108e4ab1c3fd331e80f4e73e6b9ea65fe3ec96d7136de81544000000000000000000000000000000000e4622fef26bdb9b1e8ef6591a7cc99f5b73164500c1ee224b6a761e676b8799b09a3fd4fa7e242645cc1a34708285e4",
        .name = "bls_g2mul_random*g2_unnormalized_scalar",
        .gas = 22500,
    },
    {
        .input = "00000000000000000000000000000000103121a2ceaae586d240843a398967325f8eb5a93e8fea99b62b9f88d8556c80dd726a4b30e84a36eeabaf3592937f2700000000000000000000000000000000086b990f3da2aeac0a36143b7d7c824428215140db1bb859338764cb58458f081d92664f9053b50b3fbd2e4723121b68000000000000000000000000000000000f9e7ba9a86a8f7624aa2b42dcc8772e1af4ae115685e60abc2c9b90242167acef3d0be4050bf935eed7c3b6fc7ba77e000000000000000000000000000000000d22c3652d0dc6f0fc9316e14268477c2049ef772e852108d269d9c38dba1d4802e8dae479818184c08f9a569d8784519a2b64cc58f8992cb21237914262ca9ada6cb13dc7b7d3f11c278fe0462040e4",
        .expected = "00000000000000000000000000000000036074dcbbd0e987531bfe0e45ddfbe09fd015665990ee0c352e8e403fe6af971d8f42141970d9ab14b4dd04874409e600000000000000000000000000000000019705637f24ba2f398f32c3a3e20d6a1cd0fd63e6f8f071cf603a8334f255744927e7bfdfdb18519e019c49ff6e914500000000000000000000000000000000008e74fcff4c4278c9accfb60809ed69bbcbe3d6213ef2304e078d15ec7d6decb4f462b24b8e7cc38cc11b6f2c9e0486000000000000000000000000000000001331d40100f38c1070afd832445881b47cf4d63894666d9907c85ac66604aab5ad329980938cc3c167ccc5b6bc1b8f30",
        .name = "bls_g2mul_random*p2_unnormalized_scalar",
        .gas = 22500,
    }
};

static const std::vector<test_case> BLS_G2_MSM_VALID_PRAGUE_TEST_CASES = {
    {
        .input = "00000000000000000000000000000000024aa2b2f08f0a91260805272dc51051c6e47ad4fa403b02b4510b647ae3d1770bac0326a805bbefd48056c8c121bdb80000000000000000000000000000000013e02b6052719f607dacd3a088274f65596bd0d09920b61ab5da61bbdc7f5049334cf11213945d57e5ac7d055d042b7e000000000000000000000000000000000ce5d527727d6e118cc9cdc6da2e351aadfd9baa8cbdd3a76d429a695160d12c923ac9cc3baca289e193548608b82801000000000000000000000000000000000606c4a02ea734cc32acd2b02bc28b99cb3e287e85a763af267492ab572e99ab3f370d275cec1da1aaa9075ff05f79be0000000000000000000000000000000000000000000000000000000000000011",
        .expected = "000000000000000000000000000000000ef786ebdcda12e142a32f091307f2fedf52f6c36beb278b0007a03ad81bf9fee3710a04928e43e541d02c9be44722e8000000000000000000000000000000000d05ceb0be53d2624a796a7a033aec59d9463c18d672c451ec4f2e679daef882cab7d8dd88789065156a1340ca9d426500000000000000000000000000000000118ed350274bc45e63eaaa4b8ddf119b3bf38418b5b9748597edfc456d9bc3e864ec7283426e840fd29fa84e7d89c934000000000000000000000000000000001594b866a28946b6d444bf0481558812769ea3222f5dfc961ca33e78e0ea62ee8ba63fd1ece9cc3e315abfa96d536944",
        .name = "bls_g2multiexp_single",
        .gas = 22500,
    },
    {
        .input = "00000000000000000000000000000000024aa2b2f08f0a91260805272dc51051c6e47ad4fa403b02b4510b647ae3d1770bac0326a805bbefd48056c8c121bdb80000000000000000000000000000000013e02b6052719f607dacd3a088274f65596bd0d09920b61ab5da61bbdc7f5049334cf11213945d57e5ac7d055d042b7e000000000000000000000000000000000ce5d527727d6e118cc9cdc6da2e351aadfd9baa8cbdd3a76d429a695160d12c923ac9cc3baca289e193548608b82801000000000000000000000000000000000606c4a02ea734cc32acd2b02bc28b99cb3e287e85a763af267492ab572e99ab3f370d275cec1da1aaa9075ff05f79be00000000000000000000000000000000000000000000000000000000000000320000000000000000000000000000000019d5f05b4f134bb37d89a03e87c8b729e6bdc062f3ae0ddc5265b270e40a6a5691f51ff60b764ea760651caf395101840000000000000000000000000000000015532df6a12b7c160a0831ef8321b18feb6ce7997c0718b205873608085be3afeec5b5d5251a0f85f7f5b7271271e0660000000000000000000000000000000004623ac0df1e019d337dc9488c17ef9e214dc33c63f96a90fea288e836dbd85079cb3cec42ae693e9c16af3c3204d86e0000000000000000000000000000000011ba77f71923c1b6a711a48fa4085c4885290079448a4b597030cc84aa14647136513cec6d11c4453ca74e906bbca1e1000000000000000000000000000000000000000000000000000000000000003300000000000000000000000000000000176a7158b310c9ff1bfc21b81903de99c90440792ebe6d9637652ee34acf53b43c2f31738bbc96d71dcadbbf0e3190af000000000000000000000000000000000a592641967934a97e012f7d6412c4f6ff0f177a1b466b9b49c9deb7498decc80d0c809448aa9fa6fbbb6f537515703000000000000000000000000000000000031d84356ef619e688a10247f122e1aa0d3def3e35f94043f64c634198421487ca96af5f0160384bba92bd5494506c4d000000000000000000000000000000000db8fefe735779489c957785fa8e45d24e086ef0c2aba2e3adba888f0aeee51385a82898524c443f017ee40be635048c0000000000000000000000000000000000000000000000000000000000000034",
        .expected = "00000000000000000000000000000000158d8ef3d5cdc8a1b5ce170f6eeadec450ca05952ea7457a638b8ff8b687c047799eb3dd89c2e3c6ca6c29290b64f5ab000000000000000000000000000000000807d135b6b007a101e97f5875e233b41f12bd2ffd77fe1195418a73a4c061248118ea1049aeea44750cd5ec83bcc1ae000000000000000000000000000000000f04136354f45a85a53fb68527bc8fbc7e8c1a0056878012b548a97bfdabcbd3fb8eb3ff187fbe65e1ce233afd2825050000000000000000000000000000000007b15428114e2ea094ba1e64df4c244f80aa2f75bbbf21a407bc84e80bf2a5ad787d02ae8a90cc1c137f0d898edb1684",
        .name = "bls_g2multiexp_multiple",
        .gas = 62302,
    },
    {
        .input = "00000000000000000000000000000000024aa2b2f08f0a91260805272dc51051c6e47ad4fa403b02b4510b647ae3d1770bac0326a805bbefd48056c8c121bdb80000000000000000000000000000000013e02b6052719f607dacd3a088274f65596bd0d09920b61ab5da61bbdc7f5049334cf11213945d57e5ac7d055d042b7e000000000000000000000000000000000ce5d527727d6e118cc9cdc6da2e351aadfd9baa8cbdd3a76d429a695160d12c923ac9cc3baca289e193548608b82801000000000000000000000000000000000606c4a02ea734cc32acd2b02bc28b99cb3e287e85a763af267492ab572e99ab3f370d275cec1da1aaa9075ff05f79be000000000000000000000000000000000000000000000000000000000000005b000000000000000000000000000000001638533957d540a9d2370f17cc7ed5863bc0b995b8825e0ee1ea1e1e4d00dbae81f14b0bf3611b78c952aacab827a053000000000000000000000000000000000a4edef9c1ed7f729f520e47730a124fd70662a904ba1074728114d1031e1572c6c886f6b57ec72a6178288c47c33577000000000000000000000000000000000468fb440d82b0630aeb8dca2b5256789a66da69bf91009cbfe6bd221e47aa8ae88dece9764bf3bd999d95d71e4c9899000000000000000000000000000000000f6d4552fa65dd2638b361543f887136a43253d9c66c411697003f7a13c308f5422e1aa0a59c8967acdefd8b6e36ccf3000000000000000000000000000000000000000000000000000000000000205900000000000000000000000000000000122915c824a0857e2ee414a3dccb23ae691ae54329781315a0c75df1c04d6d7a50a030fc866f09d516020ef82324afae0000000000000000000000000000000009380275bbc8e5dcea7dc4dd7e0550ff2ac480905396eda55062650f8d251c96eb480673937cc6d9d6a44aaa56ca66dc000000000000000000000000000000000b21da7955969e61010c7a1abc1a6f0136961d1e3b20b1a7326ac738fef5c721479dfd948b52fdf2455e44813ecfd8920000000000000000000000000000000008f239ba329b3967fe48d718a36cfe5f62a7e42e0bf1c1ed714150a166bfbd6bcf6b3b58b975b9edea56d53f23a0e84900000000000000000000000000000000000000000000000000000000000b7fa3000000000000000000000000000000000e7a30979a8853a077454eb63b8dcee75f106221b262886bb8e01b0abb043368da82f60899cc1412e33e4120195fc55700000000000000000000000000000000070227d3f13684fdb7ce31b8065ba3acb35f7bde6fe2ddfefa359f8b35d08a9ab9537b43e24f4ffb720b5a0bda2a82f2000000000000000000000000000000000701377cb7da22789d032737eabcea2b2eee6bb4634c4365864511a43c2caad50422993ccd3e99636eb8a5f189454b18000000000000000000000000000000000782c14e2c4ee61cbe7be6e462a66b2e3509f42d53ff333efc9bfe9a00307cd2f68b007606446d98a75fb808a405d8b90000000000000000000000000000000000000000000000000000000004165ef1000000000000000000000000000000000411a5de6730ffece671a9f21d65028cc0f1102378de124562cb1ff49db6f004fcd14d683024b0548eff3d1468df26880000000000000000000000000000000000fb837804dba8213329db46608b6c121d973363c1234a86dd183baff112709cf97096c5e9a1a770ee9d7dc641a894d60000000000000000000000000000000019b5e8f5d4a72f2b75811ac084a7f814317360bac52f6aab15eed416b4ef9938e0bdc4865cc2c4d0fd947e7c6925fd1400000000000000000000000000000000093567b4228be17ee62d11a254edd041ee4b953bffb8b8c7f925bd6662b4298bac2822b446f5b5de3b893e1be5aa49860000000000000000000000000000000000000000000000000000000173f3bfab0000000000000000000000000000000019e384121b7d70927c49e6d044fd8517c36bc6ed2813a8956dd64f049869e8a77f7e46930240e6984abe26fa6a89658f0000000000000000000000000000000003f4b4e761936d90fd5f55f99087138a07a69755ad4a46e4dd1c2cfe6d11371e1cc033111a0595e3bba98d0f538db4510000000000000000000000000000000017a31a4fccfb5f768a2157517c77a4f8aaf0dee8f260d96e02e1175a8754d09600923beae02a019afc327b65a2fdbbfc00000000000000000000000000000000088bb5832f4a4a452edda646ebaa2853a54205d56329960b44b2450070734724a74daaa401879bad142132316e9b34010000000000000000000000000000000000000000000000000000008437a521c900000000000000000000000000000000049cd1dbb2d2c3581e54c088135fef36505a6823d61b859437bfc79b617030dc8b40e32bad1fa85b9c0f368af6d38d3c000000000000000000000000000000000d0273f6bf31ed37c3b8d68083ec3d8e20b5f2cc170fa24b9b5be35b34ed013f9a921f1cad1644d4bdb14674247234c80000000000000000000000000000000008b7ae4dbf802c17a6648842922c9467e460a71c88d393ee7af356da123a2f3619e80c3bdcc8e2b1da52f8cd9913ccdd0000000000000000000000000000000005ecf93654b7a1885695aaeeb7caf41b0239dc45e1022be55d37111af2aecef87799638bec572de86a7437898efa702000000000000000000000000000000000000000000000000000002effc7b302730000000000000000000000000000000002142a58bae275564a6d63cb6bd6266ca66bef07a6ab8ca37b9d0ba2d4effbccfd89c169649f7d0e8a3eb006846579ad0000000000000000000000000000000012be651a5fa620340d418834526d37a8c932652345400b4cd9d43c8f41c080f41a6d9558118ebeab9d4268bb73e850e10000000000000000000000000000000015f4b235c209d89ce833f8f296e4cfb748e8abce6990ce1a5a914b9416c08e0d3a26db89625915c821a5f152b7fa592e0000000000000000000000000000000006fcacb3ee6650a1044852d61c9c20bedc8ee90aad97de8e24670a9ef57483e678db11dd95428915088d76e30cb01a370000000000000000000000000000000000000000000000000010b4ebfca1dee100000000000000000000000000000000018405e4b67f957b6465ead9f5afc47832d45643dc3aa03af7314c6cf980fa23dd3bb8db3358693ad06011f6a6b1a5ff000000000000000000000000000000000c48e0d4f9404ae0a7f10774c55a9e838bb09d3bae85b5eaa6b16b0f4dc2354368117f3799c37f3f7126d8b54d3f83930000000000000000000000000000000007e61f4ec5bc9e2cc8ca471ce4ed40e729b1790cd2c0d9c1cb50e615ec7f346636e77e1cf632c881c07c5385898607620000000000000000000000000000000011dfaf9281901dd356fc5dfece21898a93d9ad9e4e246dd6e18d3ee46d58ab7e77401a3e8d04057e5638ed74fb95688100000000000000000000000000000000000000000000000005f04fe2cd8a39fb000000000000000000000000000000001796abe0d9e4a703962be528e6a5cb65c60725886f925db0e2a89107ec248bb39fa332bc63bd91d28ae66e0dfce8f754000000000000000000000000000000000fb665f5a7559cb0fa1300048a0e6f1ab5547226e86f8e752dd13c28eda4168492e3d3bf2f8a6b230dd57f79b1afa9910000000000000000000000000000000003422dbbe4a06a4c6c9fdf35e54f74b4ab1528abb7249e99898e6fd7affebc7aef95bf82d328dc01d63c25f6a735c35d0000000000000000000000000000000010aa5504b469427eb3584a286191149f5c3c5a745f338278dd95337cd2336d3c4e7532d98eb189fa543824953e7c1c170000000000000000000000000000000000000000000000021c6c659f10229c390000000000000000000000000000000009303f04d568e289a35102b6df883d5ed620355c0eb5d02236718cdaf99fba6e19ef5cee2996268eb9a53ae1ee09bce3000000000000000000000000000000000190be857d602284393305bfe0a29e29a6982ed3f04ccaabafb7e59cdc7eda85c22bc3e8690355c7a0fb7590ae40f1b00000000000000000000000000000000016efd497a0c5c6b59a1fdf2b590eb67a7da8cbe72f49084e7050783ff12a783cad1859e1a0b0ec8ff784c703617670330000000000000000000000000000000017a957ea4d53f4fc8412cb015ae91b38445cdb3e7078d875c465c941e0d9a852c78d90b31b6b6010efe8bd5117e831630000000000000000000000000000000000000000000000c01a881f8abc4d8843000000000000000000000000000000000173ed58056bec9874464d3f23c3e7d3d429d6c8a167fc7f39368830eca839d0eb8260d64ca823f6c785c71f85893d8400000000000000000000000000000000123372d7d4c91a249df8f3e4f8e669087b252ab5d8cf2529a87e4ed3622e4158cf17dc44b473d5debd273261383e8a0f0000000000000000000000000000000000c500eb55ab86381a1725f339f686c7e38ce9113493736f57e999badc661b5b8494d220ded0711e841228a389abdb820000000000000000000000000000000010a4025d823c4262367c53f50e67cffa046e4a1e7c69ff30373772e49ecb310de3b313d83cc41f40a00205722f233e270000000000000000000000000000000000000000000044496e633650ef8f6fd100000000000000000000000000000000152110e866f1a6e8c5348f6e005dbd93de671b7d0fbfa04d6614bcdd27a3cb2a70f0deacb3608ba95226268481a0be7c000000000000000000000000000000000bf78a97086750eb166986ed8e428ca1d23ae3bbf8b2ee67451d7dd84445311e8bc8ab558b0bc008199f577195fc39b7000000000000000000000000000000000845be51ad0d708657bfb0da8eec64cd7779c50d90b59a3ac6a2045cad0561d654af9a84dd105cea5409d2adf286b561000000000000000000000000000000000a298f69fd652551e12219252baacab101768fc6651309450e49c7d3bb52b7547f218d12de64961aa7f059025b8e0cb500000000000000000000000000000000000000000018461a3d444ec527fcbf4b000000000000000000000000000000000027513925b419f6c581788578379995290ab9478e08ecd1999d5e1a05c58144d2f9f06fb8c7fd1586f3ef6a973a3ed7000000000000000000000000000000001292b2ce751f6f859ec7882e14083eac9841b035f9d5ed938a81579dbce07dec2c0202b7f6b25226831cd9c578e893d00000000000000000000000000000000017f36da49414d7706209d52840250eea6f33970fd7eac448ee122f24c62f6a6e09757aa29761160be0f65ba3ce7a153a00000000000000000000000000000000086d471f958f3ff679805751b183fb6310e871ba72bbdefd59c58e95ea62de0820d5affe601757e318abaa5a0c2715bd000000000000000000000000000000000000000008a0eb53c748001536d7ffa900000000000000000000000000000000090721a089bbbb130c21a529be0ede9271a91a2dde9cb2a8e091a19fd2c0a40c390ac2bda8304085c2d6e38e520eae44000000000000000000000000000000000cc64109c67b342b6dbcf86cb60fca7ad378ed6398d89076ed108685c57a07d26e40ed3d5c4b3560b21e519db5875d49000000000000000000000000000000000b0ddd488f5a6f61f087cdbf011b50209a4460c8aa8c5f48c0b30d9cf6cf24259f4e7badc42e1b7a33352949ae566fc100000000000000000000000000000000038430e8db04d205d81aa1632d23919c06f89260c7ac5850bd8b780f8388e53db3a3ddfe98cc55d1c686e582f85b0c8900000000000000000000000000000000000000031133a6c7d698078a7ec7e113000000000000000000000000000000001800ecc167bb714100f31e7610cd3fd010ca299b394c01b1a89afd11b051e92989f6336db5e6d3212f6b04673526d83900000000000000000000000000000000070401d9bba01c0445e0a682406b099f21d16d9c348cc97156769084055ca328a145c134b8c8b58f019d62882b2965de000000000000000000000000000000000287f071bda99b0318e386b27a492a6823a9664084b12acddeda34cb53f827a362ba97c0e652c37bd9d6023041d8c8d8000000000000000000000000000000000fa708ca7dd917541cd02281e525d3367b5ebf5e9353103e1f83f3b894d03d8be7e4d819c123492788855d1fdb63f2e000000000000000000000000000000000000001171d5c4909480aae3b110d01c1000000000000000000000000000000000ef786ebdcda12e142a32f091307f2fedf52f6c36beb278b0007a03ad81bf9fee3710a04928e43e541d02c9be44722e8000000000000000000000000000000000d05ceb0be53d2624a796a7a033aec59d9463c18d672c451ec4f2e679daef882cab7d8dd88789065156a1340ca9d426500000000000000000000000000000000118ed350274bc45e63eaaa4b8ddf119b3bf38418b5b9748597edfc456d9bc3e864ec7283426e840fd29fa84e7d89c934000000000000000000000000000000001594b866a28946b6d444bf0481558812769ea3222f5dfc961ca33e78e0ea62ee8ba63fd1ece9cc3e315abfa96d53694400000000000000000000000000000000000063376fcdf64c9bcbeeff0f9f9f9b0000000000000000000000000000000004b6570b4a6affe97649b0dd7a0ad0df160b37c332a8a7348dd3994cc6b1eb65623b4a9f0a3f320e7278844e261546530000000000000000000000000000000005f8fb4cf5e5313f403f15c59c79b9cebaec78291f2053c49d6427f40f2db2aa659d3a8fed7c7b07b7a5680c7b95ab5800000000000000000000000000000000045cba5ec3fa9acd1b11e1f28a01ebc028f89f96f814513453c553f58785baca8abd4150f334b405fabb925b71f4f4dd0000000000000000000000000000000013daf00b8f53af776c2e8c08d55d164aa15027611188e294230477dc1c926102088f0451222fd2eff9802db8b884ab9c00000000000000000000000000000000002344b4be368d3b617df4aa8dbdbc190000000000000000000000000000000002b29192945df0a74eed138e431962f1d39978202d247335ffbf29d8a02e982c69e96b58d7d92528baf5c422ed633f1f000000000000000000000000000000000d52c7a82fece99279de7a49439c0ff8463a637cc6003320275d69549442c95184fd75ee5e7122e5575af7432e5159290000000000000000000000000000000006ddbaad6cc16c9e62b0da9ab0196dffe92253fcfb2df9aa2076d3f16b3284997d6558cc4432d2aa1705452c4e951e6e00000000000000000000000000000000175f906a99c9d65c4647807879e5eb781532db184d28a326ef9691f8738af067b6a80147bd69327d219fad7c850a7545000000000000000000000000000000000c896c3f9d64341ba7c5f8a06271dce3000000000000000000000000000000000c86c92c9598dde7e6fc5e05d70a34c7a14cff5f400f33cf6cc26e6bf6d9a0bbc421c00f3360721f51974d76be43bd38000000000000000000000000000000001137d93502ef32471f47890a181d7823b3a86dbfcadcc930ae53952f528d617e742a52e4f243c615cc28163dc31bd80600000000000000000000000000000000088f7f8bcbc6dfcc8005b8308cd4780d574d8530e95e7831e52eb2c9a88b846852e111a8389e3d3a67accf78b08326d200000000000000000000000000000000149e43fc675dd3bde8b89cfeb29456f130bbf674cea0266bd1b2e7de23f9a7294096327b452728411ca58acc949777fa0000000000000000000000000000000474d97a9cf29e85d4a35f6102fe7984b100000000000000000000000000000000186a1da343cacf1815b9c8b6c807f536249dbfdb59d77bf4920ad2198a0d83ada21f7c39de6f06a5599f22571cab288d000000000000000000000000000000000ba1ec44f95121bd622932b84bbb4b3d279f69c494ee44db68e3165c86b627ba5e397ee197313fb5b775972798997332000000000000000000000000000000000783e7493e9fb106fa0d085e7c03eb816468d12c65d9b77643ed07c02583d491f4db5db44e565d50d8ccaa9ad8f7f8e80000000000000000000000000000000010a6a5fd90cd5f4fb6545814f5df065b001074bb3f29f649dd2612815df3a19a320f7754dd3d458e48e7fb1b4953978f00000000000000000000000000000195894e95ca3e59929612e77c1075322aeb00000000000000000000000000000000129c4945fe62538d2806fff056adac24f3bba8e17e42d82122affe6ad2123d68784348a79755f194fde3b3d448924032000000000000000000000000000000000528590e82f409ea8ce953f0c59d15080185dc6e3219b69fcaa3a2c8fc9d0b9e0bc1e75ec6c52638e6eaa4584005b5380000000000000000000000000000000018dc3e893f74729d27dd44f45a5a4f433dcd09a3b485e9d1c2bd0eb5e0e4c9024d928ddc426fdecae931e89885ee4db4000000000000000000000000000000000d6ee02e1fc7e52a8e1ef17e753065882c6fcc14da61da7ffe955fe84a9d2af9ba57562c69db3088652931bf124b0d5300000000000000000000000000009027ceef3ee429d71b58b84919d9a8d5418900000000000000000000000000000000131747485cce9a5c32837a964b8c0689ff70cb4702c6520f2220ab95192d73ae9508c5b998ffb0be40520926846ce3f100000000000000000000000000000000101e147f8bd7682b47b3a6cc0c552c26ce90b9ce0daef21f7f634b3360483afa14a11e6745e7de01a35c65b396a1a12700000000000000000000000000000000090ca61ed16c4c1e80acfef736eea2db0d7425d9110cb53e6c4a2aa3f8a59ee6c60bdce8df5825011066d44bef84d29600000000000000000000000000000000028207394adcbf30250ac21a8f1db6283580bc5e39159930552e5edb25e6215c66b6450296edc80dbc3a2acd125dab1600000000000000000000000000333e268f0b5b1adf76b88981fc305f03ce4bb30000000000000000000000000000000016cfabbe60d1e55723a0ff72cf802f2d1cf13ed131e17729adc88522a657f320a336078a9399c8e61a3bbde3d52fd3640000000000000000000000000000000009aa9a3c2a6d49d286aa593c6ff644f1786fa9ae471bdb3fe70b150a9ed7584eaa886ac057c30005c3642f65ad5581cc0000000000000000000000000000000001d417894c0cce924955a795b188b27951f8438a5485404b921a42fa79dea03c10e29d0390df2f34d7be13f360a7fada00000000000000000000000000000000189b0b3a04e6c613899d51231dbf0cba6a8a8f507ebed99d24fba7ebac6c97a8859ffde88e6d95c1a9d6b4f0a8f3c417000000000000000000000000123717b4d909628d6f3398e134a531c65a54e8a10000000000000000000000000000000016cad7807d761f2c0c6ff11e786a9ed296442de8acc50f72a87139b9f1eb7c168e1c2f0b2a1ad7f9579e1e922d0eb309000000000000000000000000000000000d3577c713fcbc0648ca8fbdda0a0bf83c726a6205ee04d2d34cacff92b58725ca3c9766206e22d0791cb232fa8a9bc3000000000000000000000000000000000f5ea1957be1b9ca8956ba5f6b1c37ea72e2529f80d7a1c61df01afcc2df6f99ced81ac0052bd0e1e83f09d76ad8d33b000000000000000000000000000000000aabced4e2b9e4a473e72bf2b1cc0ce7ab13de533107df2205ed9e2bb50fa0217e6a13abcd12fce1bda1ccf84dac237a00000000000000000000000679956d49265608468757580db6b8b1821c2eb13b",
        .expected = "000000000000000000000000000000000728c5e6e69b9103d82358cb6ba3a45a677df1c3eb3cdccf694fd71cee94f1e591b8021b0eef638cd9a1d878937b5b2d000000000000000000000000000000000ba9bcf9ccef956f2af8dc4c3fbf1cc8f3f284b04ae8710af6ef4fb36301254c777d4461858fb38fdeeb72c0d8589af5000000000000000000000000000000000224b80a57d30bce4c752664f3b5b5e3443aefa6d4e95dc334821f754b8b8d8fda4e73d03cbd4070d43b18324a686b500000000000000000000000000000000016909a02214c6c0f6682895aa99cf6cf0a22eab6f0b574437ef9c36e9df32ac3b8c5adb9f6b8827df0ccf51b16f824df",
        .name = "bls_g2multiexp_larger",
        .gas = 376875,   
    },
};

static const std::vector<test_case> BLS_MAP_G2_VALID_PRAGUE_TEST_CASES = {
    {
        .input = "0000000000000000000000000000000014406e5bfb9209256a3820879a29ac2f62d6aca82324bf3ae2aa7d3c54792043bd8c791fccdb080c1a52dc68b8b69350000000000000000000000000000000000e885bb33996e12f07da69073e2c0cc880bc8eff26d2a724299eb12d54f4bcf26f4748bb020e80a7e3794a7b0e47a641",
        .expected = "000000000000000000000000000000000d029393d3a13ff5b26fe52bd8953768946c5510f9441f1136f1e938957882db6adbd7504177ee49281ecccba596f2bf000000000000000000000000000000001993f668fb1ae603aefbb1323000033fcb3b65d8ed3bf09c84c61e27704b745f540299a1872cd697ae45a5afd780f1d600000000000000000000000000000000079cb41060ef7a128d286c9ef8638689a49ca19da8672ea5c47b6ba6dbde193ee835d3b87a76a689966037c07159c10d0000000000000000000000000000000017c688ae9a8b59a7069c27f2d58dd2196cb414f4fb89da8510518a1142ab19d158badd1c3bad03408fafb1669903cd6c",
        .name = "matter_fp2_to_g2_0",
        .gas = 23800,
    },
    {
        .input = "000000000000000000000000000000000ba1b6d79150bdc368a14157ebfe8b5f691cf657a6bbe30e79b6654691136577d2ef1b36bfb232e3336e7e4c9352a8ed000000000000000000000000000000000f12847f7787f439575031bcdb1f03cfb79f942f3a9709306e4bd5afc73d3f78fd1c1fef913f503c8cbab58453fb7df2",
        .expected = "000000000000000000000000000000000a2bca68ca23f3f03c678140d87465b5b336dbd50926d1219fcc0def162280765fe1093c117d52483d3d8cdc7ab76529000000000000000000000000000000000fe83e3a958d6038569da6132bfa19f0e3dae3bee0d8a60e7cc33e4d7084a9e8c32fe31ec6e617277e2e450699eba1f80000000000000000000000000000000005602683f0ef231cc0b7c8c695765d7933f4efa7503ed9f2aa3c774284eabcdd32fd287b6a3539c9749f2e15b58f5cd50000000000000000000000000000000000b4f17de0db6e9d081723b613b23864c1eeae91b7cbda40ecd24823022aee7fc4068adc41947b97e17009fad9d0d4de",
        .name = "matter_fp2_to_g2_1",
        .gas = 23800,
    },
    {
        .input = "000000000000000000000000000000001632336631a3c666159b6e5e1fb62ffa21488e571cffb7bc3d75d55a837f242e789a75f0f583ce2b3a969c64c2b46de200000000000000000000000000000000184f1db9ac0fdd6b5ac0307e203d0b4237a50554eb7af37bb1894d9769609c96c8437e9d6d3679ebd5f979eb04035799",
        .expected = "00000000000000000000000000000000184af3f8a359dd35dddd3dfcc6f5b55ed327907ed573378289209569244e3c9c02bdf278eb567186f8b64de380c115360000000000000000000000000000000012f5ba8e520c4730ac1fb75dabbfdc0181855e5ba2968a8c0ba36a47ab86ac45d19aa3d55f15a601e120be1f75eefe240000000000000000000000000000000004e313db704b103c2c1e3a58f8e95a470e7199081eb086e9524583131714c4a3db551fd51a3f2314a19a658e7b1765380000000000000000000000000000000004040eab7416a1703b0d103120506f1de2b26b0f48c7a0ea63dca4d9ad1c478ae03b5d7bfd51f4cd6f8cea26212c4edf",
        .name = "matter_fp2_to_g2_2",
        .gas = 23800,
    },
    {
        .input = "000000000000000000000000000000000732f171d8f6e283dd40a0324dae42ef0209c4caa0bd8ce2b12b206b6a9704f2c6015c918c79f0625fa791051b05c55c000000000000000000000000000000001139e8d932fc0ab10d6d4f6874c757c545b15be27cdb88056ed7c690aa6d924226d83e66b3e2484b2fc3dcd14418ee60",
        .expected = "0000000000000000000000000000000017fc341e495bf4ef5da4c159a28320aca97ca28fe3a0441242cf506b0f89bb52f5b5d8c6e038d229ffe67d00151912f00000000000000000000000000000000007666300b7be3d904ae3d19019f7be5cf5ba6161b969c1a78aff639a24387d8fdcc4d0e3cd81ba6f063ebf2d859370f20000000000000000000000000000000007cc705dbfb5c0418beb1cfbd864fa0631bd60eccfdb16b5d55b6ef3558e2ec87dac3b45294dcf04a064d6d1eba5a6eb00000000000000000000000000000000052cb9c982e6b05c1d2ab4eed1d8082f96426b55615ebc6a53bdc320ccad0aad044395ed641b3176b554f19e62d46b73",
        .name = "matter_fp2_to_g2_3",
        .gas = 23800,
    },
    {
        .input = "0000000000000000000000000000000019a9630cce5181fd0ad80677ed5ad8cd8bce3f284cd529175902b78ad4915f0df56f0d8b37c87c9ddb23d0342005f1570000000000000000000000000000000002cdd00b7662569c9f74553a7d0585312a776c8638e54ad016f8d9d25df98651789470b12ce2626fb3ad1373744387ac",
        .expected = "0000000000000000000000000000000015ad9155037e03898cb3b706f7105e39d413ff3a5abb65812b8d21d003cab8fbb607d3938ccd6a774bc8debfa30f42760000000000000000000000000000000019d6382bb2d78180a8998a0536d67412d00ec0ef65f4cbce01340b8d6e781c0ff790296f8cada28966b147c69e02f366000000000000000000000000000000001290c2c205b748069d0875a89ca74a3b05ad8218ed46a1570696932302983c090d96e17e0b828a666fdfc3b72cd348bc000000000000000000000000000000000114f2f7ffaa9f90b547e86c863a5d3585819a78b095848dfa39576a10874a905488687b73e613f3d426510f5d1d1ce1",
        .name = "matter_fp2_to_g2_4",
        .gas = 23800,
    },
};

TEST(Prague, blsg2add_valid)
{
    do_geth_tests<EVMC_PRAGUE>(
        "bls_g2_add_valid", BLS_G2_ADD_VALID_PRAGUE_TEST_CASES, 0x0d_address);
}

TEST(Prague, blsg2mul_valid)
{
    do_geth_tests<EVMC_PRAGUE>(
        "bls_g2_mul_valid", BLS_G2_MUL_VALID_PRAGUE_TEST_CASES, 0x0e_address);
}

TEST(Prague, blsg2msm_valid)
{
    do_geth_tests<EVMC_PRAGUE>(
        "bls_g2_msm_valid", BLS_G2_MSM_VALID_PRAGUE_TEST_CASES, 0x0e_address);
}

TEST(Prague, bls_map_g2_valid)
{
    do_geth_tests<EVMC_PRAGUE>(
        "bls12_map_fp2_to_g2_valid", BLS_MAP_G2_VALID_PRAGUE_TEST_CASES, 0x11_address);
}

static const std::vector<test_case> BLS_G1_ADD_INVALID_PRAGUE_TEST_CASES = {
    {
        .input = "",
        .expected = "",
        .name = "bls_g1add_empty_input",
        .gas = 375,
    },
    {
        .input = "0000000000000000000000000000000017f1d3a73197d7942695638c4fa9ac0fc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bb00000000000000000000000000000008b3f481e3aaa0f1a09e30ed741d8ae4fcf5e095d5d00af600db18cb2c04b3edd03cc744a2888ae40caa232946c5e7e10000000000000000000000000000000017f1d3a73197d7942695638c4fa9ac0fc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bb0000000000000000000000000000000008b3f481e3aaa0f1a09e30ed741d8ae4fcf5e095d5d00af600db18cb2c04b3edd03cc744a2888ae40caa232946c5e7e1",
        .expected = "",
        .name = "bls_g1add_short_input",
        .gas = 375,
    },
    {
        .input = "0000000000000000000000000000000017f1d3a73197d7942695638c4fa9ac0fc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bb000000000000000000000000000000000008b3f481e3aaa0f1a09e30ed741d8ae4fcf5e095d5d00af600db18cb2c04b3edd03cc744a2888ae40caa232946c5e7e10000000000000000000000000000000017f1d3a73197d7942695638c4fa9ac0fc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bb0000000000000000000000000000000008b3f481e3aaa0f1a09e30ed741d8ae4fcf5e095d5d00af600db18cb2c04b3edd03cc744a2888ae40caa232946c5e7e1",
        .expected = "",
        .name = "bls_g1add_large_input",
        .gas = 375,
    },
    {
        .input = "0000000000000000000000000000000017f1d3a73197d7942695638c4fa9ac0fc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bb0000000000000000000000000000000108b3f481e3aaa0f1a09e30ed741d8ae4fcf5e095d5d00af600db18cb2c04b3edd03cc744a2888ae40caa232946c5e7e10000000000000000000000000000000017f1d3a73197d7942695638c4fa9ac0fc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bb0000000000000000000000000000000008b3f481e3aaa0f1a09e30ed741d8ae4fcf5e095d5d00af600db18cb2c04b3edd03cc744a2888ae40caa232946c5e7e1",
        .expected = "",
        .name = "bls_g1add_violate_top_bytes",
        .gas = 375,
    },
    {
        .input = "0000000000000000000000000000000017f1d3a73197d7942695638c4fa9ac0fc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bb000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaac0000000000000000000000000000000017f1d3a73197d7942695638c4fa9ac0fc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bb0000000000000000000000000000000008b3f481e3aaa0f1a09e30ed741d8ae4fcf5e095d5d00af600db18cb2c04b3edd03cc744a2888ae40caa232946c5e7e1",
        .expected = "",
        .name = "bls_g1add_invalid_field_element",
        .gas = 375,
    },
    {
        .input = "00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000017f1d3a73197d7942695638c4fa9ac0fc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bb0000000000000000000000000000000008b3f481e3aaa0f1a09e30ed741d8ae4fcf5e095d5d00af600db18cb2c04b3edd03cc744a2888ae40caa232946c5e7e1",
        .expected = "",
        .name = "bls_g1add_point_not_on_curve",
        .gas = 375,
    },
};

static const std::vector<test_case> BLS_G1_MUL_INVALID_PRAGUE_TEST_CASES = {
    {
        .input = "",
        .expected = "",
        .name = "bls_g1mul_empty_input",
        .gas = 22500,
    },
    {
        .input = "00000000000000000000000000000017f1d3a73197d7942695638c4fa9ac0fc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bb0000000000000000000000000000000008b3f481e3aaa0f1a09e30ed741d8ae4fcf5e095d5d00af600db18cb2c04b3edd03cc744a2888ae40caa232946c5e7e10000000000000000000000000000000000000000000000000000000000000002",
        .expected = "",
        .name = "bls_g1mul_short_input",
        .gas = 22500,
    },
    {
        .input = "000000000000000000000000000000000017f1d3a73197d7942695638c4fa9ac0fc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bb0000000000000000000000000000000008b3f481e3aaa0f1a09e30ed741d8ae4fcf5e095d5d00af600db18cb2c04b3edd03cc744a2888ae40caa232946c5e7e10000000000000000000000000000000000000000000000000000000000000002",
        .expected = "",
        .name = "bls_g1mul_large_input",
        .gas = 22500,
    },
    {
        .input = "0000000000000000000000000000000031f2e5916b17be2e71b10b4292f558e727dfd7d48af9cbc5087f0ce00dcca27c8b01e83eaace1aefb539f00adb2271660000000000000000000000000000000008b3f481e3aaa0f1a09e30ed741d8ae4fcf5e095d5d00af600db18cb2c04b3edd03cc744a2888ae40caa232946c5e7e10000000000000000000000000000000000000000000000000000000000000002",
        .expected = "",
        .name = "bls_g1mul_invalid_field_element",
        .gas = 22500,
    },
    {
        .input = "0000000000000000000000000000000017f1d3a73197d7942695638c4fa9ac0fc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bb00000000000000000000000000000000186b28d92356c4dfec4b5201ad099dbdede3781f8998ddf929b4cd7756192185ca7b8f4ef7088f813270ac3d48868a210000000000000000000000000000000000000000000000000000000000000002",
        .expected = "",
        .name = "bls_g1mul_point_not_on_curve",
        .gas = 22500,
    },
    {
        .input = "1000000000000000000000000000000017f1d3a73197d7942695638c4fa9ac0fc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bb0000000000000000000000000000000008b3f481e3aaa0f1a09e30ed741d8ae4fcf5e095d5d00af600db18cb2c04b3edd03cc744a2888ae40caa232946c5e7e10000000000000000000000000000000000000000000000000000000000000002",
        .expected = "",
        .name = "bls_g1mul_violate_top_bytes",
        .gas = 22500,
    },
    {
        .input = "000000000000000000000000000000000123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef00000000000000000000000000000000193fb7cedb32b2c3adc06ec11a96bc0d661869316f5e4a577a9f7c179593987beb4fb2ee424dbb2f5dd891e228b46c4a0000000000000000000000000000000000000000000000000000000000000002",
        .expected = "",
        .name = "bls_g1mul_g1_not_in_correct_subgroup",
        .gas = 22500,
    }
};

static const std::vector<test_case> BLS_G1_MSM_INVALID_PRAGUE_TEST_CASES = {
    {
        .input = "",
        .expected = "",
        .name = "bls_g1multiexp_empty_input",
        .gas = 22500,
    },
    {
        .input = "0000000000000000000000000000000017f1d3a73197d7942695638c4fa9ac0fc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bb00000000000000000000000000000008b3f481e3aaa0f1a09e30ed741d8ae4fcf5e095d5d00af600db18cb2c04b3edd03cc744a2888ae40caa232946c5e7e10000000000000000000000000000000000000000000000000000000000000007",
        .expected = "",
        .name = "bls_g1multiexp_short_input",
        .gas = 22500,
    },
    {
        .input = "0000000000000000000000000000000017f1d3a73197d7942695638c4fa9ac0fc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bb000000000000000000000000000000000008b3f481e3aaa0f1a09e30ed741d8ae4fcf5e095d5d00af600db18cb2c04b3edd03cc744a2888ae40caa232946c5e7e10000000000000000000000000000000000000000000000000000000000000007",
        .expected = "",
        .name = "bls_g1multiexp_large_input",
        .gas = 22500,
    },
    {
        .input = "0000000000000000000000000000000017f1d3a73197d7942695638c4fa9ac0fc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bb000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaac0000000000000000000000000000000000000000000000000000000000000007",
        .expected = "",
        .name = "bls_g1multiexp_invalid_field_element",
        .gas = 22500,
    },
    {
        .input = "0000000000000000000000000000000017f1d3a73197d7942695638c4fa9ac0fc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bb0000000000000000000000000000000108b3f481e3aaa0f1a09e30ed741d8ae4fcf5e095d5d00af600db18cb2c04b3edd03cc744a2888ae40caa232946c5e7e10000000000000000000000000000000000000000000000000000000000000007",
        .expected = "",
        .name = "bls_g1multiexp_violate_top_bytes",
        .gas = 22500,
    },
    {
        .input = "00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000001",
        .expected = "",
        .name = "bls_g1multiexp_point_not_on_curve",
        .gas = 22776,
    },
    {
        .input = "000000000000000000000000000000000123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef00000000000000000000000000000000193fb7cedb32b2c3adc06ec11a96bc0d661869316f5e4a577a9f7c179593987beb4fb2ee424dbb2f5dd891e228b46c4a000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000112b98340eee2777cc3c14163dea3ec97977ac3dc5c70da32e6e87578f44912e902ccef9efe28d4a78b8999dfbca942600000000000000000000000000000000186b28d92356c4dfec4b5201ad099dbdede3781f8998ddf929b4cd7756192185ca7b8f4ef7088f813270ac3d48868a210000000000000000000000000000000000000000000000000000000000000002",
        .expected = "",
        .name = "bls_g1multiexp_g1_not_in_correct_subgroup",
        .gas = 22776,
    }
};

static const std::vector<test_case> BLS_MAP_G1_INVALID_PRAGUE_TEST_CASES = {
    {
        .input = "",
        .expected = "",
        .name = "bls_g1mul_empty_input",
        .gas = 5500,
    },
    {
        .input = "00000000000000000000000000000017f1d3a73197d7942695638c4fa9ac0fc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bb0000000000000000000000000000000008b3f481e3aaa0f1a09e30ed741d8ae4fcf5e095d5d00af600db18cb2c04b3edd03cc744a2888ae40caa232946c5e7e10000000000000000000000000000000000000000000000000000000000000002",
        .expected = "",
        .name = "bls_g1mul_short_input",
        .gas = 5500,
    },
    {
        .input = "000000000000000000000000000000000017f1d3a73197d7942695638c4fa9ac0fc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bb0000000000000000000000000000000008b3f481e3aaa0f1a09e30ed741d8ae4fcf5e095d5d00af600db18cb2c04b3edd03cc744a2888ae40caa232946c5e7e10000000000000000000000000000000000000000000000000000000000000002",
        .expected = "",
        .name = "bls_g1mul_large_input",
        .gas = 5500,
    },
    {
        .input = "0000000000000000000000000000000031f2e5916b17be2e71b10b4292f558e727dfd7d48af9cbc5087f0ce00dcca27c8b01e83eaace1aefb539f00adb2271660000000000000000000000000000000008b3f481e3aaa0f1a09e30ed741d8ae4fcf5e095d5d00af600db18cb2c04b3edd03cc744a2888ae40caa232946c5e7e10000000000000000000000000000000000000000000000000000000000000002",
        .expected = "",
        .name = "bls_g1mul_invalid_field_element",
        .gas = 5500,
    },
};

TEST(Prague, blsg1add_invalid)
{
    do_geth_tests<EVMC_PRAGUE>(
        "bls_g1_add_invalid", BLS_G1_ADD_INVALID_PRAGUE_TEST_CASES, 0x0b_address);
}

TEST(Prague, blsg1mul_invalid)
{
    do_geth_tests<EVMC_PRAGUE>(
        "bls_g1_mul_invalid", BLS_G1_MUL_INVALID_PRAGUE_TEST_CASES, 0x0c_address);
}

TEST(Prague, blsg1msm_invalid)
{
    do_geth_tests<EVMC_PRAGUE>(
        "bls_g1_msm_invalid", BLS_G1_MSM_INVALID_PRAGUE_TEST_CASES, 0x0c_address);
}

TEST(Prague, bls_map_g1_invalid)
{
    do_geth_tests<EVMC_PRAGUE>(
        "bls12_map_fp_to_g1_valid", BLS_MAP_G1_INVALID_PRAGUE_TEST_CASES, 0x10_address);
}

static const std::vector<test_case> BLS_G2_ADD_INVALID_PRAGUE_TEST_CASES = {
    {
        .input = "",
        .expected = "",
        .name = "bls_g2add_empty_input",
        .gas = 600,
    },
    {
        .input = "00000000000000000000000000000000024aa2b2f08f0a91260805272dc51051c6e47ad4fa403b02b4510b647ae3d1770bac0326a805bbefd48056c8c121bdb80000000000000000000000000000000013e02b6052719f607dacd3a088274f65596bd0d09920b61ab5da61bbdc7f5049334cf11213945d57e5ac7d055d042b7e000000000000000000000000000000000ce5d527727d6e118cc9cdc6da2e351aadfd9baa8cbdd3a76d429a695160d12c923ac9cc3baca289e193548608b828010000000000000000000000000000000606c4a02ea734cc32acd2b02bc28b99cb3e287e85a763af267492ab572e99ab3f370d275cec1da1aaa9075ff05f79be00000000000000000000000000000000024aa2b2f08f0a91260805272dc51051c6e47ad4fa403b02b4510b647ae3d1770bac0326a805bbefd48056c8c121bdb80000000000000000000000000000000013e02b6052719f607dacd3a088274f65596bd0d09920b61ab5da61bbdc7f5049334cf11213945d57e5ac7d055d042b7e000000000000000000000000000000000ce5d527727d6e118cc9cdc6da2e351aadfd9baa8cbdd3a76d429a695160d12c923ac9cc3baca289e193548608b82801000000000000000000000000000000000606c4a02ea734cc32acd2b02bc28b99cb3e287e85a763af267492ab572e99ab3f370d275cec1da1aaa9075ff05f79be",
        .expected = "",
        .name = "bls_g2add_short_input",
        .gas = 600,
    },
    {
        .input = "00000000000000000000000000000000024aa2b2f08f0a91260805272dc51051c6e47ad4fa403b02b4510b647ae3d1770bac0326a805bbefd48056c8c121bdb80000000000000000000000000000000013e02b6052719f607dacd3a088274f65596bd0d09920b61ab5da61bbdc7f5049334cf11213945d57e5ac7d055d042b7e000000000000000000000000000000000ce5d527727d6e118cc9cdc6da2e351aadfd9baa8cbdd3a76d429a695160d12c923ac9cc3baca289e193548608b8280100000000000000000000000000000000000606c4a02ea734cc32acd2b02bc28b99cb3e287e85a763af267492ab572e99ab3f370d275cec1da1aaa9075ff05f79be00000000000000000000000000000000024aa2b2f08f0a91260805272dc51051c6e47ad4fa403b02b4510b647ae3d1770bac0326a805bbefd48056c8c121bdb80000000000000000000000000000000013e02b6052719f607dacd3a088274f65596bd0d09920b61ab5da61bbdc7f5049334cf11213945d57e5ac7d055d042b7e000000000000000000000000000000000ce5d527727d6e118cc9cdc6da2e351aadfd9baa8cbdd3a76d429a695160d12c923ac9cc3baca289e193548608b82801000000000000000000000000000000000606c4a02ea734cc32acd2b02bc28b99cb3e287e85a763af267492ab572e99ab3f370d275cec1da1aaa9075ff05f79be",
        .expected = "",
        .name = "bls_g2add_large_input",
        .gas = 600,
    },
    {
        .input = "00000000000000000000000000000000024aa2b2f08f0a91260805272dc51051c6e47ad4fa403b02b4510b647ae3d1770bac0326a805bbefd48056c8c121bdb80000000000000000000000000000000013e02b6052719f607dacd3a088274f65596bd0d09920b61ab5da61bbdc7f5049334cf11213945d57e5ac7d055d042b7e000000000000000000000000000000000ce5d527727d6e118cc9cdc6da2e351aadfd9baa8cbdd3a76d429a695160d12c923ac9cc3baca289e193548608b82801000000000000000000000000000000010606c4a02ea734cc32acd2b02bc28b99cb3e287e85a763af267492ab572e99ab3f370d275cec1da1aaa9075ff05f79be00000000000000000000000000000000024aa2b2f08f0a91260805272dc51051c6e47ad4fa403b02b4510b647ae3d1770bac0326a805bbefd48056c8c121bdb80000000000000000000000000000000013e02b6052719f607dacd3a088274f65596bd0d09920b61ab5da61bbdc7f5049334cf11213945d57e5ac7d055d042b7e000000000000000000000000000000000ce5d527727d6e118cc9cdc6da2e351aadfd9baa8cbdd3a76d429a695160d12c923ac9cc3baca289e193548608b82801000000000000000000000000000000000606c4a02ea734cc32acd2b02bc28b99cb3e287e85a763af267492ab572e99ab3f370d275cec1da1aaa9075ff05f79be",
        .expected = "",
        .name = "bls_g2add_violate_top_bytes",
        .gas = 600,
    },
    {
        .input = "00000000000000000000000000000000024aa2b2f08f0a91260805272dc51051c6e47ad4fa403b02b4510b647ae3d1770bac0326a805bbefd48056c8c121bdb80000000000000000000000000000000013e02b6052719f607dacd3a088274f65596bd0d09920b61ab5da61bbdc7f5049334cf11213945d57e5ac7d055d042b7e000000000000000000000000000000000ce5d527727d6e118cc9cdc6da2e351aadfd9baa8cbdd3a76d429a695160d12c923ac9cc3baca289e193548608b82801000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaac00000000000000000000000000000000024aa2b2f08f0a91260805272dc51051c6e47ad4fa403b02b4510b647ae3d1770bac0326a805bbefd48056c8c121bdb80000000000000000000000000000000013e02b6052719f607dacd3a088274f65596bd0d09920b61ab5da61bbdc7f5049334cf11213945d57e5ac7d055d042b7e000000000000000000000000000000000ce5d527727d6e118cc9cdc6da2e351aadfd9baa8cbdd3a76d429a695160d12c923ac9cc3baca289e193548608b82801000000000000000000000000000000000606c4a02ea734cc32acd2b02bc28b99cb3e287e85a763af267492ab572e99ab3f370d275cec1da1aaa9075ff05f79be",
        .expected = "",
        .name = "bls_g2add_invalid_field_element",
        .gas = 600,
    },
    {
        .input = "0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000024aa2b2f08f0a91260805272dc51051c6e47ad4fa403b02b4510b647ae3d1770bac0326a805bbefd48056c8c121bdb80000000000000000000000000000000013e02b6052719f607dacd3a088274f65596bd0d09920b61ab5da61bbdc7f5049334cf11213945d57e5ac7d055d042b7e000000000000000000000000000000000ce5d527727d6e118cc9cdc6da2e351aadfd9baa8cbdd3a76d429a695160d12c923ac9cc3baca289e193548608b82801000000000000000000000000000000000606c4a02ea734cc32acd2b02bc28b99cb3e287e85a763af267492ab572e99ab3f370d275cec1da1aaa9075ff05f79be",
        .expected = "",
        .name = "bls_g2add_point_not_on_curve",
        .gas = 600,
    }
};

static const std::vector<test_case> BLS_G2_MUL_INVALID_PRAGUE_TEST_CASES = {
    {
        .input = "",
        .expected = "",
        .name = "bls_g2add_empty_input",
        .gas = 22500,
    },
    {
        .input = "000000000000000000000000000000024aa2b2f08f0a91260805272dc51051c6e47ad4fa403b02b4510b647ae3d1770bac0326a805bbefd48056c8c121bdb80000000000000000000000000000000013e02b6052719f607dacd3a088274f65596bd0d09920b61ab5da61bbdc7f5049334cf11213945d57e5ac7d055d042b7e000000000000000000000000000000000ce5d527727d6e118cc9cdc6da2e351aadfd9baa8cbdd3a76d429a695160d12c923ac9cc3baca289e193548608b82801000000000000000000000000000000000606c4a02ea734cc32acd2b02bc28b99cb3e287e85a763af267492ab572e99ab3f370d275cec1da1aaa9075ff05f79be0000000000000000000000000000000000000000000000000000000000000002",
        .expected = "",
        .name = "bls_g2mul_short_input",
        .gas = 22500,
    },
    {
        .input = "0000000000000000000000000000000000024aa2b2f08f0a91260805272dc51051c6e47ad4fa403b02b4510b647ae3d1770bac0326a805bbefd48056c8c121bdb80000000000000000000000000000000013e02b6052719f607dacd3a088274f65596bd0d09920b61ab5da61bbdc7f5049334cf11213945d57e5ac7d055d042b7e000000000000000000000000000000000ce5d527727d6e118cc9cdc6da2e351aadfd9baa8cbdd3a76d429a695160d12c923ac9cc3baca289e193548608b82801000000000000000000000000000000000606c4a02ea734cc32acd2b02bc28b99cb3e287e85a763af267492ab572e99ab3f370d275cec1da1aaa9075ff05f79be0000000000000000000000000000000000000000000000000000000000000002",
        .expected = "",
        .name = "bls_g2mul_large_input",
        .gas = 22500,
    },
    {
        .input = "000000000000000000000000000000001c4bb49d2a0ef12b7123acdd7110bd292b5bc659edc54dc21b81de057194c79b2a5803255959bbef8e7f56c8c12168630000000000000000000000000000000013e02b6052719f607dacd3a088274f65596bd0d09920b61ab5da61bbdc7f5049334cf11213945d57e5ac7d055d042b7e000000000000000000000000000000000ce5d527727d6e118cc9cdc6da2e351aadfd9baa8cbdd3a76d429a695160d12c923ac9cc3baca289e193548608b82801000000000000000000000000000000000606c4a02ea734cc32acd2b02bc28b99cb3e287e85a763af267492ab572e99ab3f370d275cec1da1aaa9075ff05f79be0000000000000000000000000000000000000000000000000000000000000002",
        .expected = "",
        .name = "bls_g2mul_invalid_field_element",
        .gas = 22500,
    },
    {
        .input = "00000000000000000000000000000000024aa2b2f08f0a91260805272dc51051c6e47ad4fa403b02b4510b647ae3d1770bac0326a805bbefd48056c8c121bdb800000000000000000000000000000000086b990f3da2aeac0a36143b7d7c824428215140db1bb859338764cb58458f081d92664f9053b50b3fbd2e4723121b68000000000000000000000000000000000ce5d527727d6e118cc9cdc6da2e351aadfd9baa8cbdd3a76d429a695160d12c923ac9cc3baca289e193548608b82801000000000000000000000000000000000606c4a02ea734cc32acd2b02bc28b99cb3e287e85a763af267492ab572e99ab3f370d275cec1da1aaa9075ff05f79be0000000000000000000000000000000000000000000000000000000000000002",
        .expected = "",
        .name = "bls_g2mul_point_not_on_curve",
        .gas = 22500,
    },
    {
        .input = "10000000000000000000000000000000024aa2b2f08f0a91260805272dc51051c6e47ad4fa403b02b4510b647ae3d1770bac0326a805bbefd48056c8c121bdb80000000000000000000000000000000013e02b6052719f607dacd3a088274f65596bd0d09920b61ab5da61bbdc7f5049334cf11213945d57e5ac7d055d042b7e000000000000000000000000000000000ce5d527727d6e118cc9cdc6da2e351aadfd9baa8cbdd3a76d429a695160d12c923ac9cc3baca289e193548608b82801000000000000000000000000000000000606c4a02ea734cc32acd2b02bc28b99cb3e287e85a763af267492ab572e99ab3f370d275cec1da1aaa9075ff05f79be0000000000000000000000000000000000000000000000000000000000000002",
        .expected = "",
        .name = "bls_g2mul_violate_top_bytes",
        .gas = 22500,
    },
    {
        .input = "00000000000000000000000000000000197bfd0342bbc8bee2beced2f173e1a87be576379b343e93232d6cef98d84b1d696e5612ff283ce2cfdccb2cfb65fa0c00000000000000000000000000000000184e811f55e6f9d84d77d2f79102fd7ea7422f4759df5bf7f6331d550245e3f1bcf6a30e3b29110d85e0ca16f9f6ae7a000000000000000000000000000000000f10e1eb3c1e53d2ad9cf2d398b2dc22c5842fab0a74b174f691a7e914975da3564d835cd7d2982815b8ac57f507348f000000000000000000000000000000000767d1c453890f1b9110fda82f5815c27281aba3f026ee868e4176a0654feea41a96575e0c4d58a14dbfbcc05b5010b10000000000000000000000000000000000000000000000000000000000000002",
        .expected = "",
        .name = "bls_g2mul_g2_not_in_correct_subgroup",
        .gas = 22500,
    }
};

static const std::vector<test_case> BLS_G2_MSM_INVALID_PRAGUE_TEST_CASES {
    {
        .input = "",
        .expected = "",
        .name = "bls_g2multiexp_empty_input",
        .gas = 22500
    },
    {
        .input = "00000000000000000000000000000000024aa2b2f08f0a91260805272dc51051c6e47ad4fa403b02b4510b647ae3d1770bac0326a805bbefd48056c8c121bdb80000000000000000000000000000000013e02b6052719f607dacd3a088274f65596bd0d09920b61ab5da61bbdc7f5049334cf11213945d57e5ac7d055d042b7e000000000000000000000000000000000ce5d527727d6e118cc9cdc6da2e351aadfd9baa8cbdd3a76d429a695160d12c923ac9cc3baca289e193548608b828010000000000000000000000000000000606c4a02ea734cc32acd2b02bc28b99cb3e287e85a763af267492ab572e99ab3f370d275cec1da1aaa9075ff05f79be0000000000000000000000000000000000000000000000000000000000000007",
        .expected = "",
        .name = "bls_g2multiexp_short_input",
        .gas = 22500
    },
    {
        .input = "00000000000000000000000000000000024aa2b2f08f0a91260805272dc51051c6e47ad4fa403b02b4510b647ae3d1770bac0326a805bbefd48056c8c121bdb80000000000000000000000000000000013e02b6052719f607dacd3a088274f65596bd0d09920b61ab5da61bbdc7f5049334cf11213945d57e5ac7d055d042b7e000000000000000000000000000000000ce5d527727d6e118cc9cdc6da2e351aadfd9baa8cbdd3a76d429a695160d12c923ac9cc3baca289e193548608b8280100000000000000000000000000000000000606c4a02ea734cc32acd2b02bc28b99cb3e287e85a763af267492ab572e99ab3f370d275cec1da1aaa9075ff05f79be0000000000000000000000000000000000000000000000000000000000000007",
       .expected = "",
        .name = "bls_g2multiexp_large_input",
        .gas = 22500
    },
    {
        .input = "00000000000000000000000000000000024aa2b2f08f0a91260805272dc51051c6e47ad4fa403b02b4510b647ae3d1770bac0326a805bbefd48056c8c121bdb80000000000000000000000000000000013e02b6052719f607dacd3a088274f65596bd0d09920b61ab5da61bbdc7f5049334cf11213945d57e5ac7d055d042b7e000000000000000000000000000000000ce5d527727d6e118cc9cdc6da2e351aadfd9baa8cbdd3a76d429a695160d12c923ac9cc3baca289e193548608b82801000000000000000000000000000000010606c4a02ea734cc32acd2b02bc28b99cb3e287e85a763af267492ab572e99ab3f370d275cec1da1aaa9075ff05f79be0000000000000000000000000000000000000000000000000000000000000007",
        .expected = "",
        .name = "bls_g2multiexp_violate_top_bytes",
        .gas = 22500
    },
    {
        .input = "00000000000000000000000000000000024aa2b2f08f0a91260805272dc51051c6e47ad4fa403b02b4510b647ae3d1770bac0326a805bbefd48056c8c121bdb80000000000000000000000000000000013e02b6052719f607dacd3a088274f65596bd0d09920b61ab5da61bbdc7f5049334cf11213945d57e5ac7d055d042b7e000000000000000000000000000000000ce5d527727d6e118cc9cdc6da2e351aadfd9baa8cbdd3a76d429a695160d12c923ac9cc3baca289e193548608b82801000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaac0000000000000000000000000000000000000000000000000000000000000007",
        .expected = "",
        .name = "bls_g2multiexp_invalid_field_element",
        .gas = 22500
    },
    {
        .input = "000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000001",
        .expected = "",
        .name = "bls_g2multiexp_point_not_on_curve",
        .gas = 22500
    },
    {
        .input = "00000000000000000000000000000000197bfd0342bbc8bee2beced2f173e1a87be576379b343e93232d6cef98d84b1d696e5612ff283ce2cfdccb2cfb65fa0c00000000000000000000000000000000184e811f55e6f9d84d77d2f79102fd7ea7422f4759df5bf7f6331d550245e3f1bcf6a30e3b29110d85e0ca16f9f6ae7a000000000000000000000000000000000f10e1eb3c1e53d2ad9cf2d398b2dc22c5842fab0a74b174f691a7e914975da3564d835cd7d2982815b8ac57f507348f000000000000000000000000000000000767d1c453890f1b9110fda82f5815c27281aba3f026ee868e4176a0654feea41a96575e0c4d58a14dbfbcc05b5010b1000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000103121a2ceaae586d240843a398967325f8eb5a93e8fea99b62b9f88d8556c80dd726a4b30e84a36eeabaf3592937f2700000000000000000000000000000000086b990f3da2aeac0a36143b7d7c824428215140db1bb859338764cb58458f081d92664f9053b50b3fbd2e4723121b68000000000000000000000000000000000f9e7ba9a86a8f7624aa2b42dcc8772e1af4ae115685e60abc2c9b90242167acef3d0be4050bf935eed7c3b6fc7ba77e000000000000000000000000000000000d22c3652d0dc6f0fc9316e14268477c2049ef772e852108d269d9c38dba1d4802e8dae479818184c08f9a569d8784510000000000000000000000000000000000000000000000000000000000000002",
        .expected = "",
        .name = "bls_pairing_g2_not_in_correct_subgroup",
        .gas = 22500
    }
};

static const std::vector<test_case> BLS_MAP_G2_INVALID_PRAGUE_TEST_CASES {
    {
        .input = "",
        .expected = "",
        .name = "bls_mapg2_empty_input",
        .gas = 23800,
    },
    {
        .input = "0000000000000000000000000000000007355d25caf6e7f2f0cb2812ca0e513bd026ed09dda65b177500fa31714e09ea0ded3a078b526bed3307f804d4b93b040000000000000000000000000000000002829ce3c021339ccb5caf3e187f6370e1e2a311dec9b75363117063ab2015603ff52c3d3b98f19c2f65575e99e8b7",
        .expected = "",
        .name = "bls_mapg2_short_input",
        .gas = 23800,
    },
    {
        .input = "000000000000000000000000000000000007355d25caf6e7f2f0cb2812ca0e513bd026ed09dda65b177500fa31714e09ea0ded3a078b526bed3307f804d4b93b040000000000000000000000000000000002829ce3c021339ccb5caf3e187f6370e1e2a311dec9b75363117063ab2015603ff52c3d3b98f19c2f65575e99e8b78c",
        .expected = "",
        .name = "bls_mapg2_long_input",
        .gas = 23800,
    },
    {
        .input = "000000000000000000000000000000000007355d25caf6e7f2f0cb2812ca0e513bd026ed09dda65b177500fa31714e09ea0ded3a078b526bed3307f804d4b93b040000000000000000000000000000000002829ce3c021339ccb5caf3e187f6370e1e2a311dec9b75363117063ab2015603ff52c3d3b98f19c2f65575e99e8b7",
        .expected = "",
        .name = "bls_mapg2_top_bytes",
        .gas = 23800,
    },
    {
        .input = "0000000000000000000000000000000021366f100476ce8d3be6cfc90d59fe13349e388ed12b6dd6dc31ccd267ff000e2c993a063ca66beced06f804d4b8e5af0000000000000000000000000000000002829ce3c021339ccb5caf3e187f6370e1e2a311dec9b75363117063ab2015603ff52c3d3b98f19c2f65575e99e8b78c",
        .expected = "",
        .name = "bls_mapg2_invalid_fq_element",
        .gas = 23800,
    }
};

TEST(Prague, blsg2add_invalid)
{
    do_geth_tests<EVMC_PRAGUE>(
        "bls_g2_add_invalid", BLS_G2_ADD_INVALID_PRAGUE_TEST_CASES, 0x0d_address);
}

TEST(Prague, blsg2mul_invalid)
{
    do_geth_tests<EVMC_PRAGUE>(
        "bls_g2_mul_invalid", BLS_G2_MUL_INVALID_PRAGUE_TEST_CASES, 0x0e_address);
}

TEST(Prague, blsg2msm_invalid)
{
    do_geth_tests<EVMC_PRAGUE>(
        "bls_g2_msm_invalid", BLS_G2_MSM_INVALID_PRAGUE_TEST_CASES, 0x0e_address);
}

TEST(Prague, bls_map_g2_invalid)
{
    do_geth_tests<EVMC_PRAGUE>(
        "bls12_map_fp2_to_g2_valid", BLS_MAP_G2_INVALID_PRAGUE_TEST_CASES, 0x11_address);
}

static const std::vector<test_case> BLS_PAIRING_CHECK_VALID_PRAGUE_TEST_CASES {
    {
        .input = "000000000000000000000000000000000572cbea904d67468808c8eb50a9450c9721db309128012543902d0ac358a62ae28f75bb8f1c7c42c39a8c5529bf0f4e00000000000000000000000000000000166a9d8cabc673a322fda673779d8e3822ba3ecb8670e461f73bb9021d5fd76a4c56d9d4cd16bd1bba86881979749d2800000000000000000000000000000000122915c824a0857e2ee414a3dccb23ae691ae54329781315a0c75df1c04d6d7a50a030fc866f09d516020ef82324afae0000000000000000000000000000000009380275bbc8e5dcea7dc4dd7e0550ff2ac480905396eda55062650f8d251c96eb480673937cc6d9d6a44aaa56ca66dc000000000000000000000000000000000b21da7955969e61010c7a1abc1a6f0136961d1e3b20b1a7326ac738fef5c721479dfd948b52fdf2455e44813ecfd8920000000000000000000000000000000008f239ba329b3967fe48d718a36cfe5f62a7e42e0bf1c1ed714150a166bfbd6bcf6b3b58b975b9edea56d53f23a0e8490000000000000000000000000000000006e82f6da4520f85c5d27d8f329eccfa05944fd1096b20734c894966d12a9e2a9a9744529d7212d33883113a0cadb9090000000000000000000000000000000017d81038f7d60bee9110d9c0d6d1102fe2d998c957f28e31ec284cc04134df8e47e8f82ff3af2e60a6d9688a4563477c00000000000000000000000000000000024aa2b2f08f0a91260805272dc51051c6e47ad4fa403b02b4510b647ae3d1770bac0326a805bbefd48056c8c121bdb80000000000000000000000000000000013e02b6052719f607dacd3a088274f65596bd0d09920b61ab5da61bbdc7f5049334cf11213945d57e5ac7d055d042b7e000000000000000000000000000000000d1b3cc2c7027888be51d9ef691d77bcb679afda66c73f17f9ee3837a55024f78c71363275a75d75d86bab79f74782aa0000000000000000000000000000000013fa4d4a0ad8b1ce186ed5061789213d993923066dddaf1040bc3ff59f825c78df74f2d75467e25e0f55f8a00fa030ed",
        .expected = "0000000000000000000000000000000000000000000000000000000000000001",
        .name = "bls_pairing_e(2*G1,3*G2)=e(6*G1,G2)",
        .gas = 102900,
    },
    {
        .input = "000000000000000000000000000000000572cbea904d67468808c8eb50a9450c9721db309128012543902d0ac358a62ae28f75bb8f1c7c42c39a8c5529bf0f4e00000000000000000000000000000000166a9d8cabc673a322fda673779d8e3822ba3ecb8670e461f73bb9021d5fd76a4c56d9d4cd16bd1bba86881979749d2800000000000000000000000000000000122915c824a0857e2ee414a3dccb23ae691ae54329781315a0c75df1c04d6d7a50a030fc866f09d516020ef82324afae0000000000000000000000000000000009380275bbc8e5dcea7dc4dd7e0550ff2ac480905396eda55062650f8d251c96eb480673937cc6d9d6a44aaa56ca66dc000000000000000000000000000000000b21da7955969e61010c7a1abc1a6f0136961d1e3b20b1a7326ac738fef5c721479dfd948b52fdf2455e44813ecfd8920000000000000000000000000000000008f239ba329b3967fe48d718a36cfe5f62a7e42e0bf1c1ed714150a166bfbd6bcf6b3b58b975b9edea56d53f23a0e8490000000000000000000000000000000010e7791fb972fe014159aa33a98622da3cdc98ff707965e536d8636b5fcc5ac7a91a8c46e59a00dca575af0f18fb13dc0000000000000000000000000000000016ba437edcc6551e30c10512367494bfb6b01cc6681e8a4c3cd2501832ab5c4abc40b4578b85cbaffbf0bcd70d67c6e200000000000000000000000000000000024aa2b2f08f0a91260805272dc51051c6e47ad4fa403b02b4510b647ae3d1770bac0326a805bbefd48056c8c121bdb80000000000000000000000000000000013e02b6052719f607dacd3a088274f65596bd0d09920b61ab5da61bbdc7f5049334cf11213945d57e5ac7d055d042b7e000000000000000000000000000000000d1b3cc2c7027888be51d9ef691d77bcb679afda66c73f17f9ee3837a55024f78c71363275a75d75d86bab79f74782aa0000000000000000000000000000000013fa4d4a0ad8b1ce186ed5061789213d993923066dddaf1040bc3ff59f825c78df74f2d75467e25e0f55f8a00fa030ed",
        .expected = "0000000000000000000000000000000000000000000000000000000000000000",
        .name = "bls_pairing_e(2*G1,3*G2)=e(5*G1,G2)",
        .gas = 102900,
    },
    {
        .input = "0000000000000000000000000000000000fd75ebcc0a21649e3177bcce15426da0e4f25d6828fbf4038d4d7ed3bd4421de3ef61d70f794687b12b2d571971a550000000000000000000000000000000004523f5a3915fc57ee889cdb057e3e76109112d125217546ccfe26810c99b130d1b27820595ad61c7527dc5bbb132a9000000000000000000000000000000000186a1da343cacf1815b9c8b6c807f536249dbfdb59d77bf4920ad2198a0d83ada21f7c39de6f06a5599f22571cab288d000000000000000000000000000000000ba1ec44f95121bd622932b84bbb4b3d279f69c494ee44db68e3165c86b627ba5e397ee197313fb5b775972798997332000000000000000000000000000000000783e7493e9fb106fa0d085e7c03eb816468d12c65d9b77643ed07c02583d491f4db5db44e565d50d8ccaa9ad8f7f8e80000000000000000000000000000000010a6a5fd90cd5f4fb6545814f5df065b001074bb3f29f649dd2612815df3a19a320f7754dd3d458e48e7fb1b4953978f000000000000000000000000000000000345dd80ffef0eaec8920e39ebb7f5e9ae9c1d6179e9129b705923df7830c67f3690cbc48649d4079eadf5397339580c00000000000000000000000000000000083d3baf25e42f2845d8fa594dda2e0f40a4d670dda40f30da0aff0d81c87ac3d687fe84eca72f34c7c755a045668cf100000000000000000000000000000000129c4945fe62538d2806fff056adac24f3bba8e17e42d82122affe6ad2123d68784348a79755f194fde3b3d448924032000000000000000000000000000000000528590e82f409ea8ce953f0c59d15080185dc6e3219b69fcaa3a2c8fc9d0b9e0bc1e75ec6c52638e6eaa4584005b5380000000000000000000000000000000018dc3e893f74729d27dd44f45a5a4f433dcd09a3b485e9d1c2bd0eb5e0e4c9024d928ddc426fdecae931e89885ee4db4000000000000000000000000000000000d6ee02e1fc7e52a8e1ef17e753065882c6fcc14da61da7ffe955fe84a9d2af9ba57562c69db3088652931bf124b0d5300000000000000000000000000000000051f8a0b82a6d86202a61cbc3b0f3db7d19650b914587bde4715ccd372e1e40cab95517779d840416e1679c84a6db24e000000000000000000000000000000000b6a63ac48b7d7666ccfcf1e7de0097c5e6e1aacd03507d23fb975d8daec42857b3a471bf3fc471425b63864e045f4df00000000000000000000000000000000131747485cce9a5c32837a964b8c0689ff70cb4702c6520f2220ab95192d73ae9508c5b998ffb0be40520926846ce3f100000000000000000000000000000000101e147f8bd7682b47b3a6cc0c552c26ce90b9ce0daef21f7f634b3360483afa14a11e6745e7de01a35c65b396a1a12700000000000000000000000000000000090ca61ed16c4c1e80acfef736eea2db0d7425d9110cb53e6c4a2aa3f8a59ee6c60bdce8df5825011066d44bef84d29600000000000000000000000000000000028207394adcbf30250ac21a8f1db6283580bc5e39159930552e5edb25e6215c66b6450296edc80dbc3a2acd125dab160000000000000000000000000000000019bef05aaba1ea467fcbc9c420f5e3153c9d2b5f9bf2c7e2e7f6946f854043627b45b008607b9a9108bb96f3c1c089d3000000000000000000000000000000000adb3250ba142db6a748a85e4e401fa0490dd10f27068d161bd47cb562cc189b3194ab53a998e48a48c65e071bb541170000000000000000000000000000000016cfabbe60d1e55723a0ff72cf802f2d1cf13ed131e17729adc88522a657f320a336078a9399c8e61a3bbde3d52fd3640000000000000000000000000000000009aa9a3c2a6d49d286aa593c6ff644f1786fa9ae471bdb3fe70b150a9ed7584eaa886ac057c30005c3642f65ad5581cc0000000000000000000000000000000001d417894c0cce924955a795b188b27951f8438a5485404b921a42fa79dea03c10e29d0390df2f34d7be13f360a7fada00000000000000000000000000000000189b0b3a04e6c613899d51231dbf0cba6a8a8f507ebed99d24fba7ebac6c97a8859ffde88e6d95c1a9d6b4f0a8f3c417000000000000000000000000000000000d9e19b3f4c7c233a6112e5397309f9812a4f61f754f11dd3dcb8b07d55a7b1dfea65f19a1488a14fef9a414950835820000000000000000000000000000000009d0d1f706f1a85a98f3efaf5c35a41c9182afc129285cf2db3212f6ea0da586ca539bc66181f2ccb228485dd8aff0a70000000000000000000000000000000016cad7807d761f2c0c6ff11e786a9ed296442de8acc50f72a87139b9f1eb7c168e1c2f0b2a1ad7f9579e1e922d0eb309000000000000000000000000000000000d3577c713fcbc0648ca8fbdda0a0bf83c726a6205ee04d2d34cacff92b58725ca3c9766206e22d0791cb232fa8a9bc3000000000000000000000000000000000f5ea1957be1b9ca8956ba5f6b1c37ea72e2529f80d7a1c61df01afcc2df6f99ced81ac0052bd0e1e83f09d76ad8d33b000000000000000000000000000000000aabced4e2b9e4a473e72bf2b1cc0ce7ab13de533107df2205ed9e2bb50fa0217e6a13abcd12fce1bda1ccf84dac237a00000000000000000000000000000000073eb991aa22cdb794da6fcde55a427f0a4df5a4a70de23a988b5e5fc8c4d844f66d990273267a54dd21579b7ba6a086000000000000000000000000000000001825bacd18f695351f843521ebeada20352c3c3965626f98bc4c68e6ff7c4eed38b48f328204bbb9cd461511d24ebfb3000000000000000000000000000000000029ea93c2f1eb48b195815571ea0148198ff1b19462618cab08d037646b592ecab5a66b4bc660ffd02d1b996ca377da000000000000000000000000000000000bb319a4550c981ee89e3c7e6dcc434283454847792807940f72fd2dbf3625b092e0a0c03e581fd9bd9cf74f95ccef15000000000000000000000000000000000abb072b8d9011e81c9f5b23ba86fdb6399c878aa4eadee45fb2486afe594dffc53be643598a23e5428894a36f5ac3ce0000000000000000000000000000000005d04aa0b644faae17d4c76a14aa680c69fdfc6b59fee3ef45641f566165fced60cbbda4ca096e132bb6f58ab4516686000000000000000000000000000000001098f178f84fc753a76bb63709e9be91eec3ff5f7f3a5f4836f34fe8a1a6d6c5578d8fd820573cef3a01e2bfef3eaf3a000000000000000000000000000000000ea923110b733b531006075f796cc9368f2477fe26020f465468efbb380ce1f8eebaf5c770f31d320f9bd378dc758436000000000000000000000000000000001065f2a2d29a997343765f239c99a018490eced40ac42fc93217dfe20d8b43ee2215f65166aff483b3dc042c5a43b196000000000000000000000000000000000766e4c66f4a442ff1f61a7a4d197d2b47dd226d0e7822a9b065108cfc643cd3f3d5ae59ed2ce4cde13fd9260bb5b7cc0000000000000000000000000000000012251cc6abbabeb7bbe1fdd63eaee10832a748fff24f7e3fdccaea87facb6e99f2e0407a38f27f90450a471b873104620000000000000000000000000000000011181e08c8fba91271adfee9d31681f8412ab7a3f754f7ba4709024c0ad2287e32dd455d71a296b4838072a8ab9d96f2000000000000000000000000000000001252a4ac3529f8b2b6e8189b95a60b8865f07f9a9b73f98d5df708511d3f68632c4c7d1e2b03e6b1d1e2c01839752ada0000000000000000000000000000000002a1bc189e36902d1a49b9965eca3cb818ab5c26dffca63ca9af032870f7bbc615ac65f21bed27bd77dd65f2e90f53580000000000000000000000000000000005a7445f55add1ed5c143424ceef3d594280e316c9441a8e68c3ad97377141d015bf878bdfcf0df9fbcd0529f4e8100800000000000000000000000000000000192b52ba08ed509fc84d5775a7182498fd1ff80941d673c53470c9c9f1192f9c0057d68a1dfee0c68fe5df3625cc43bf000000000000000000000000000000000d3fcaf2f727e0eb32c65da9b910dc681b948dda874d0db6f6ed3f063430fbf073385a9a14c2dd78568726124e2b3ea8000000000000000000000000000000001943ce22cdb2387bd5796950dc95d1ace4012ab9bb4afb46223760230c1709e075f1ae76d6b3f2e947ba6b16d458ccd1000000000000000000000000000000001271205227c7aa27f45f20b3ba380dfea8b51efae91fd32e552774c99e2a1237aa59c0c43f52aad99bba3783ea2f36a4000000000000000000000000000000001407ffc2c1a2fe3b00d1f91e1f4febcda31004f7c301075c9031c55dd3dfa8104b156a6a3b7017fccd27f81c2af222ef000000000000000000000000000000000a29e38da2d42fd4712052800c7c8dd6e94fd9f506e946068aaac799d60b94c2d7515769ffdd32ea95d3910330ec47de000000000000000000000000000000000c60dae92451206390e30b5daa7151d63624dee496753c87dd54eadc92dc9602081fae02a1a53bac97e984a571923a5d00000000000000000000000000000000085f4fda4c72328895f20c683cb49603a37ff2c43d62f66602506dad5b8d1daebfbac7a7db3f50ccf4dfff277deb105c0000000000000000000000000000000005674d005457e0fe1f0fd978d63996c5f3d29f9149ee4eb04c464742dd329ccaef5e5f6b896d986ddfc9f1b2a3aec13100000000000000000000000000000000071bc66d6e2d244afc4a5ce4da1dce3d0c22c303ba61310fdf57843bbd97763ef496833dfa99d14be084bb1a039bb2da0000000000000000000000000000000012c22e047b0af8e2f4bf3bd3633ef0f8264004ca8ea5677a468857a1762f815235a479e53f4ad4741ffda3fb855021c900000000000000000000000000000000024aa2b2f08f0a91260805272dc51051c6e47ad4fa403b02b4510b647ae3d1770bac0326a805bbefd48056c8c121bdb80000000000000000000000000000000013e02b6052719f607dacd3a088274f65596bd0d09920b61ab5da61bbdc7f5049334cf11213945d57e5ac7d055d042b7e000000000000000000000000000000000d1b3cc2c7027888be51d9ef691d77bcb679afda66c73f17f9ee3837a55024f78c71363275a75d75d86bab79f74782aa0000000000000000000000000000000013fa4d4a0ad8b1ce186ed5061789213d993923066dddaf1040bc3ff59f825c78df74f2d75467e25e0f55f8a00fa030ed",
        .expected = "0000000000000000000000000000000000000000000000000000000000000001",
        .name = "bls_pairing_10paircheckstrue",
        .gas = 363700,
    },
};

TEST(Prague, bls_pairing_check_valid)
{
    do_geth_tests<EVMC_PRAGUE>(
        "bls12_pairing_check_valid", BLS_PAIRING_CHECK_VALID_PRAGUE_TEST_CASES, 0x0f_address);
}

static const std::vector<test_case> BLS_PAIRING_CHECK_INVALID_PRAGUE_TEST_CASES {
    {
        .input = "",
        .expected = "",
        .name = "bls_pairing_empty_input",
        .gas = 363700,
    },
    {
        .input = "00000000000000000000000000000017f1d3a73197d7942695638c4fa9ac0fc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bb0000000000000000000000000000000008b3f481e3aaa0f1a09e30ed741d8ae4fcf5e095d5d00af600db18cb2c04b3edd03cc744a2888ae40caa232946c5e7e100000000000000000000000000000000024aa2b2f08f0a91260805272dc51051c6e47ad4fa403b02b4510b647ae3d1770bac0326a805bbefd48056c8c121bdb80000000000000000000000000000000013e02b6052719f607dacd3a088274f65596bd0d09920b61ab5da61bbdc7f5049334cf11213945d57e5ac7d055d042b7e000000000000000000000000000000000ce5d527727d6e118cc9cdc6da2e351aadfd9baa8cbdd3a76d429a695160d12c923ac9cc3baca289e193548608b82801000000000000000000000000000000000606c4a02ea734cc32acd2b02bc28b99cb3e287e85a763af267492ab572e99ab3f370d275cec1da1aaa9075ff05f79be0000000000000000000000000000000017f1d3a73197d7942695638c4fa9ac0fc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bb0000000000000000000000000000000008b3f481e3aaa0f1a09e30ed741d8ae4fcf5e095d5d00af600db18cb2c04b3edd03cc744a2888ae40caa232946c5e7e100000000000000000000000000000000024aa2b2f08f0a91260805272dc51051c6e47ad4fa403b02b4510b647ae3d1770bac0326a805bbefd48056c8c121bdb80000000000000000000000000000000013e02b6052719f607dacd3a088274f65596bd0d09920b61ab5da61bbdc7f5049334cf11213945d57e5ac7d055d042b7e000000000000000000000000000000000d1b3cc2c7027888be51d9ef691d77bcb679afda66c73f17f9ee3837a55024f78c71363275a75d75d86bab79f74782aa0000000000000000000000000000000013fa4d4a0ad8b1ce186ed5061789213d993923066dddaf1040bc3ff59f825c78df74f2d75467e25e0f55f8a00fa030ed",
        .expected = "",
        .name = "bls_pairing_missing_data",
        .gas = 363700,
    },
    {
        .input = "0000000000000000000000000000000017f1d3a73197d7942695638c4fa9ac0fc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bb0000000000000000000000000000000008b3f481e3aaa0f1a09e30ed741d8ae4fcf5e095d5d00af600db18cb2c04b3edd03cc744a2888ae40caa232946c5e7e100000000000000000000000000000000024aa2b2f08f0a91260805272dc51051c6e47ad4fa403b02b4510b647ae3d1770bac0326a805bbefd48056c8c121bdb80000000000000000000000000000000013e02b6052719f607dacd3a088274f65596bd0d09920b61ab5da61bbdc7f5049334cf11213945d57e5ac7d055d042b7e000000000000000000000000000000000ce5d527727d6e118cc9cdc6da2e351aadfd9baa8cbdd3a76d429a695160d12c923ac9cc3baca289e193548608b82801000000000000000000000000000000000606c4a02ea734cc32acd2b02bc28b99cb3e287e85a763af267492ab572e99ab3f370d275cec1da1aaa9075ff05f79be0000000000000000000000000000000017f1d3a73197d7942695638c4fa9ac0fc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bb0000000000000000000000000000000008b3f481e3aaa0f1a09e30ed741d8ae4fcf5e095d5d00af600db18cb2c04b3edd03cc744a2888ae40caa232946c5e7e100000000000000000000000000000000024aa2b2f08f0a91260805272dc51051c6e47ad4fa403b02b4510b647ae3d1770bac0326a805bbefd48056c8c121bdb80000000000000000000000000000000013e02b6052719f607dacd3a088274f65596bd0d09920b61ab5da61bbdc7f5049334cf11213945d57e5ac7d055d042b7e000000000000000000000000000000000ce5d527727d6e118cc9cdc6da2e351aadfd9baa8cbdd3a76d429a695160d12c923ac9cc3baca289e193548608b8280100000000000000000000000000000000000606c4a02ea734cc32acd2b02bc28b99cb3e287e85a763af267492ab572e99ab3f370d275cec1da1aaa9075ff05f79be",
        .expected = "",
        .name = "bls_pairing_extra_data",
        .gas = 363700,
    },
    {
        .input = "0000000000000000000000000000000017f1d3a73197d7942695638c4fa9ac0fc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bb0000000000000000000000000000000008b3f481e3aaa0f1a09e30ed741d8ae4fcf5e095d5d00af600db18cb2c04b3edd03cc744a2888ae40caa232946c5e7e100000000000000000000000000000000024aa2b2f08f0a91260805272dc51051c6e47ad4fa403b02b4510b647ae3d1770bac0326a805bbefd48056c8c121bdb80000000000000000000000000000000013e02b6052719f607dacd3a088274f65596bd0d09920b61ab5da61bbdc7f5049334cf11213945d57e5ac7d055d042b7e000000000000000000000000000000000ce5d527727d6e118cc9cdc6da2e351aadfd9baa8cbdd3a76d429a695160d12c923ac9cc3baca289e193548608b82801000000000000000000000000000000000606c4a02ea734cc32acd2b02bc28b99cb3e287e85a763af267492ab572e99ab3f370d275cec1da1aaa9075ff05f79be0000000000000000000000000000000017f1d3a73197d7942695638c4fa9ac0fc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bb0000000000000000000000000000000008b3f481e3aaa0f1a09e30ed741d8ae4fcf5e095d5d00af600db18cb2c04b3edd03cc744a2888ae40caa232946c5e7e100000000000000000000000000000000024aa2b2f08f0a91260805272dc51051c6e47ad4fa403b02b4510b647ae3d1770bac0326a805bbefd48056c8c121bdb80000000000000000000000000000000013e02b6052719f607dacd3a088274f65596bd0d09920b61ab5da61bbdc7f5049334cf11213945d57e5ac7d055d042b7e000000000000000000000000000000000ce5d527727d6e118cc9cdc6da2e351aadfd9baa8cbdd3a76d429a695160d12c923ac9cc3baca289e193548608b82801000000000000000000000000000000001a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaac",
        .expected = "",
        .name = "bls_pairing_invalid_field_element",
        .gas = 363700,
    },
    {
        .input = "0000000000000000000000000000000017f1d3a73197d7942695638c4fa9ac0fc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bb0000000000000000000000000000000008b3f481e3aaa0f1a09e30ed741d8ae4fcf5e095d5d00af600db18cb2c04b3edd03cc744a2888ae40caa232946c5e7e100000000000000000000000000000000024aa2b2f08f0a91260805272dc51051c6e47ad4fa403b02b4510b647ae3d1770bac0326a805bbefd48056c8c121bdb80000000000000000000000000000000013e02b6052719f607dacd3a088274f65596bd0d09920b61ab5da61bbdc7f5049334cf11213945d57e5ac7d055d042b7e000000000000000000000000000000000ce5d527727d6e118cc9cdc6da2e351aadfd9baa8cbdd3a76d429a695160d12c923ac9cc3baca289e193548608b82801000000000000000000000000000000000606c4a02ea734cc32acd2b02bc28b99cb3e287e85a763af267492ab572e99ab3f370d275cec1da1aaa9075ff05f79be0000000000000000000000000000000017f1d3a73197d7942695638c4fa9ac0fc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bb0000000000000000000000000000000008b3f481e3aaa0f1a09e30ed741d8ae4fcf5e095d5d00af600db18cb2c04b3edd03cc744a2888ae40caa232946c5e7e100000000000000000000000000000000024aa2b2f08f0a91260805272dc51051c6e47ad4fa403b02b4510b647ae3d1770bac0326a805bbefd48056c8c121bdb80000000000000000000000000000000013e02b6052719f607dacd3a088274f65596bd0d09920b61ab5da61bbdc7f5049334cf11213945d57e5ac7d055d042b7e000000000000000000000000000000000ce5d527727d6e118cc9cdc6da2e351aadfd9baa8cbdd3a76d429a695160d12c923ac9cc3baca289e193548608b82801000000000000000000000000000000010606c4a02ea734cc32acd2b02bc28b99cb3e287e85a763af267492ab572e99ab3f370d275cec1da1aaa9075ff05f79be",
        .expected = "",
        .name = "bls_pairing_top_bytes",
        .gas = 363700,
    },
    {
        .input = "0000000000000000000000000000000017f1d3a73197d7942695638c4fa9ac0fc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bb0000000000000000000000000000000008b3f481e3aaa0f1a09e30ed741d8ae4fcf5e095d5d00af600db18cb2c04b3edd03cc744a2888ae40caa232946c5e7e100000000000000000000000000000000024aa2b2f08f0a91260805272dc51051c6e47ad4fa403b02b4510b647ae3d1770bac0326a805bbefd48056c8c121bdb80000000000000000000000000000000013e02b6052719f607dacd3a088274f65596bd0d09920b61ab5da61bbdc7f5049334cf11213945d57e5ac7d055d042b7e000000000000000000000000000000000ce5d527727d6e118cc9cdc6da2e351aadfd9baa8cbdd3a76d429a695160d12c923ac9cc3baca289e193548608b82801000000000000000000000000000000000606c4a02ea734cc32acd2b02bc28b99cb3e287e85a763af267492ab572e99ab3f370d275cec1da1aaa9075ff05f79be000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000024aa2b2f08f0a91260805272dc51051c6e47ad4fa403b02b4510b647ae3d1770bac0326a805bbefd48056c8c121bdb80000000000000000000000000000000013e02b6052719f607dacd3a088274f65596bd0d09920b61ab5da61bbdc7f5049334cf11213945d57e5ac7d055d042b7e000000000000000000000000000000000ce5d527727d6e118cc9cdc6da2e351aadfd9baa8cbdd3a76d429a695160d12c923ac9cc3baca289e193548608b82801000000000000000000000000000000000606c4a02ea734cc32acd2b02bc28b99cb3e287e85a763af267492ab572e99ab3f370d275cec1da1aaa9075ff05f79be",
        .expected = "",
        .name = "bls_pairing_g1_not_on_curve",
        .gas = 363700,
    },
    {
        .input = "0000000000000000000000000000000017f1d3a73197d7942695638c4fa9ac0fc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bb0000000000000000000000000000000008b3f481e3aaa0f1a09e30ed741d8ae4fcf5e095d5d00af600db18cb2c04b3edd03cc744a2888ae40caa232946c5e7e100000000000000000000000000000000024aa2b2f08f0a91260805272dc51051c6e47ad4fa403b02b4510b647ae3d1770bac0326a805bbefd48056c8c121bdb80000000000000000000000000000000013e02b6052719f607dacd3a088274f65596bd0d09920b61ab5da61bbdc7f5049334cf11213945d57e5ac7d055d042b7e000000000000000000000000000000000ce5d527727d6e118cc9cdc6da2e351aadfd9baa8cbdd3a76d429a695160d12c923ac9cc3baca289e193548608b82801000000000000000000000000000000000606c4a02ea734cc32acd2b02bc28b99cb3e287e85a763af267492ab572e99ab3f370d275cec1da1aaa9075ff05f79be0000000000000000000000000000000017f1d3a73197d7942695638c4fa9ac0fc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bb0000000000000000000000000000000008b3f481e3aaa0f1a09e30ed741d8ae4fcf5e095d5d00af600db18cb2c04b3edd03cc744a2888ae40caa232946c5e7e100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001",
        .expected = "",
        .name = "bls_pairing_g2_not_on_curve",
        .gas = 363700,
    },
    {
        .input = "0000000000000000000000000000000017f1d3a73197d7942695638c4fa9ac0fc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bb0000000000000000000000000000000008b3f481e3aaa0f1a09e30ed741d8ae4fcf5e095d5d00af600db18cb2c04b3edd03cc744a2888ae40caa232946c5e7e100000000000000000000000000000000024aa2b2f08f0a91260805272dc51051c6e47ad4fa403b02b4510b647ae3d1770bac0326a805bbefd48056c8c121bdb80000000000000000000000000000000013e02b6052719f607dacd3a088274f65596bd0d09920b61ab5da61bbdc7f5049334cf11213945d57e5ac7d055d042b7e000000000000000000000000000000000ce5d527727d6e118cc9cdc6da2e351aadfd9baa8cbdd3a76d429a695160d12c923ac9cc3baca289e193548608b82801000000000000000000000000000000000606c4a02ea734cc32acd2b02bc28b99cb3e287e85a763af267492ab572e99ab3f370d275cec1da1aaa9075ff05f79be00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000a989badd40d6212b33cffc3f3763e9bc760f988c9926b26da9dd85e928483446346b8ed00e1de5d5ea93e354abe706c00000000000000000000000000000000024aa2b2f08f0a91260805272dc51051c6e47ad4fa403b02b4510b647ae3d1770bac0326a805bbefd48056c8c121bdb80000000000000000000000000000000013e02b6052719f607dacd3a088274f65596bd0d09920b61ab5da61bbdc7f5049334cf11213945d57e5ac7d055d042b7e000000000000000000000000000000000ce5d527727d6e118cc9cdc6da2e351aadfd9baa8cbdd3a76d429a695160d12c923ac9cc3baca289e193548608b82801000000000000000000000000000000000606c4a02ea734cc32acd2b02bc28b99cb3e287e85a763af267492ab572e99ab3f370d275cec1da1aaa9075ff05f79be",
        .expected = "",
        .name = "bls_pairing_g1_not_in_correct_subgroup",
        .gas = 363700,
    },
    {
        .input = "0000000000000000000000000000000017f1d3a73197d7942695638c4fa9ac0fc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bb0000000000000000000000000000000008b3f481e3aaa0f1a09e30ed741d8ae4fcf5e095d5d00af600db18cb2c04b3edd03cc744a2888ae40caa232946c5e7e100000000000000000000000000000000024aa2b2f08f0a91260805272dc51051c6e47ad4fa403b02b4510b647ae3d1770bac0326a805bbefd48056c8c121bdb80000000000000000000000000000000013e02b6052719f607dacd3a088274f65596bd0d09920b61ab5da61bbdc7f5049334cf11213945d57e5ac7d055d042b7e000000000000000000000000000000000ce5d527727d6e118cc9cdc6da2e351aadfd9baa8cbdd3a76d429a695160d12c923ac9cc3baca289e193548608b82801000000000000000000000000000000000606c4a02ea734cc32acd2b02bc28b99cb3e287e85a763af267492ab572e99ab3f370d275cec1da1aaa9075ff05f79be0000000000000000000000000000000017f1d3a73197d7942695638c4fa9ac0fc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bb0000000000000000000000000000000008b3f481e3aaa0f1a09e30ed741d8ae4fcf5e095d5d00af600db18cb2c04b3edd03cc744a2888ae40caa232946c5e7e1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000013a59858b6809fca4d9a3b6539246a70051a3c88899964a42bc9a69cf9acdd9dd387cfa9086b894185b9a46a402be730000000000000000000000000000000002d27e0ec3356299a346a09ad7dc4ef68a483c3aed53f9139d2f929a3eecebf72082e5e58c6da24ee32e03040c406d4f",
        .expected = "",
        .name = "bls_pairing_g2_not_in_correct_subgroup",
        .gas = 363700,
    }
};

TEST(Prague, bls_pairing_check_invalid)
{
    do_geth_tests<EVMC_PRAGUE>(
        "bls12_pairing_check_invalid", BLS_PAIRING_CHECK_INVALID_PRAGUE_TEST_CASES, 0x0f_address);
}