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
#include <category/execution/ethereum/state2/block_state.hpp>
#include <category/vm/evm/traits.hpp>

#include <evmc/evmc.h>
#include <evmc/evmc.hpp>
#include <evmc/hex.hpp>

#include <gtest/gtest.h>

#include <nlohmann/json.hpp>

#include <cstddef>
#include <cstdint>
#include <filesystem>
#include <fstream>
#include <iterator>
#include <string_view>
#include <vector>

#include "test_resource_data.h"

using namespace monad;

using namespace evmc::literals;

namespace fs = std::filesystem;

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

struct test_case
{
    std::string input;
    std::string expected;
    std::string name;
    int64_t gas;
};

void from_json(nlohmann::json const &j, test_case &t)
{
    t.input = j.at("Input");
    t.expected = j.value("Expected", "");
    t.name = j.at("Name");

    // Expected-to-fail tests don't have a Gas field, so we assign them the
    // maximum gas value to prevent out-of-gas errors from masking the actual
    // failure the test is expected to trigger.
    t.gas = j.value("Gas", std::numeric_limits<decltype(t.gas)>::max());
}

std::vector<test_case> load_test_cases(fs::path const &json_path)
{
    MONAD_ASSERT(fs::is_regular_file(json_path));
    std::ifstream in(json_path);
    return nlohmann::json::parse(in);
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
    InMemoryMachine machine;
    mpt::Db db{machine};
    TrieDb tdb{db};
    vm::VM vm;
    BlockState bs{tdb, vm};
    State s{bs, Incarnation{0, 0}};

    for (size_t i = 0; i < num_basic_test_cases; i++) {
        auto const &basic_test_case = basic_test_cases[i];

        evmc::Result const result =
            check_call_precompile<EvmTraits<EVMC_BERLIN>>(
                s, basic_test_case.input)
                .value();

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

template <Traits traits = EvmTraits<EVMC_BERLIN>>
void do_geth_tests(
    char const *suite_name, std::vector<test_case> const &test_cases,
    monad::Address const &code_address)
{
    InMemoryMachine machine;
    mpt::Db db{machine};
    TrieDb tdb{db};
    vm::VM vm;
    BlockState bs{tdb, vm};
    State s{bs, Incarnation{0, 0}};

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
                check_call_precompile<traits>(s, input).value();

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

template <Traits traits = EvmTraits<EVMC_BERLIN>>
void do_geth_tests(
    char const *suite_name, std::string_view json_path,
    monad::Address const &code_address)
{
    auto const tests =
        load_test_cases(test_resource::geth_vectors_dir / json_path);
    do_geth_tests<traits>(suite_name, tests, code_address);
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

TEST(SpuriousDragonThroughByzantium, modular_exponentiation)
{
    do_geth_tests<EvmTraits<EVMC_BYZANTIUM>>(
        "Modular Exponentiation", "modexp.json", 0x05_address);
}

TEST(SpuriousDragonThroughByzantium, bn_add)
{
    // Before https://eips.ethereum.org/EIPS/eip-1108
    auto const tests = transform_test_cases(
        load_test_cases(test_resource::geth_vectors_dir / "bn256Add.json"),
        [](auto &test) { test.gas = 500; });

    do_geth_tests<EvmTraits<EVMC_BYZANTIUM>>("bn_add", tests, 0x06_address);
}

TEST(SpuriousDragonThroughByzantium, bn_mul)
{
    // Before https://eips.ethereum.org/EIPS/eip-1108
    auto const tests = transform_test_cases(
        load_test_cases(
            test_resource::geth_vectors_dir / "bn256ScalarMul.json"),
        [](auto &test) { test.gas = 40'000; });

    do_geth_tests<EvmTraits<EVMC_BYZANTIUM>>("bn_mul", tests, 0x07_address);
}

TEST(SpuriousDragonThroughByzantium, bn_pairing)
{
    // Before https://eips.ethereum.org/EIPS/eip-1108
    auto const tests = transform_test_cases(
        load_test_cases(test_resource::geth_vectors_dir / "bn256Pairing.json"),
        [](auto &test) {
            // k = input size in bytes / 192; input here is a hex formatted
            // string so divide by 192 * 2 to find k
            auto const k = test.input.size() / 384;
            test.gas = static_cast<int64_t>(80'000 * k + 100'000);
        });

    do_geth_tests<EvmTraits<EVMC_BYZANTIUM>>("bn_pairing", tests, 0x08_address);
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
    do_geth_tests<EvmTraits<EVMC_ISTANBUL>>(
        "Modular Exponentiation", "modexp.json", 0x05_address);
}

TEST(Istanbul, bn_add)
{
    do_geth_tests<EvmTraits<EVMC_ISTANBUL>>(
        "bn_add", "bn256Add.json", 0x06_address);
}

TEST(Istanbul, bn_mul)
{
    do_geth_tests<EvmTraits<EVMC_ISTANBUL>>(
        "bn_mul", "bn256ScalarMul.json", 0x07_address);
}

TEST(Istanbul, bn_pairing)
{
    do_geth_tests<EvmTraits<EVMC_ISTANBUL>>(
        "bn_pairing", "bn256Pairing.json", 0x08_address);
}

TEST(Istanbul, blake2f_valid)
{
    do_geth_tests<EvmTraits<EVMC_ISTANBUL>>(
        "blake_2f_valid", "blake2F.json", 0x09_address);
}

TEST(Istanbul, blake2f_invalid)
{
    do_geth_tests("blake_2f_invalid", "fail-blake2f.json", 0x09_address);
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

TEST(Berlin, modular_exponentiation)
{
    do_geth_tests<EvmTraits<EVMC_BERLIN>>(
        "Modular Exponentiation", "modexp_eip2565.json", 0x05_address);
}

TEST(Berlin, bn_add)
{
    do_geth_tests<EvmTraits<EVMC_BERLIN>>(
        "bn_add", "bn256Add.json", 0x06_address);
}

TEST(Berlin, bn_mul)
{
    do_geth_tests<EvmTraits<EVMC_BERLIN>>(
        "bn_mul", "bn256ScalarMul.json", 0x07_address);
}

TEST(Berlin, bn_pairing)
{
    do_geth_tests<EvmTraits<EVMC_BERLIN>>(
        "bn_pairing", "bn256Pairing.json", 0x08_address);
}

TEST(Berlin, blake2f_valid)
{
    // the test cases did not change from the previous fork
    do_geth_tests<EvmTraits<EVMC_BERLIN>>(
        "blake_2f_valid", "blake2F.json", 0x09_address);
}

TEST(Berlin, blake2f_invalid)
{
    // the test cases did not change from the previous fork
    do_geth_tests<EvmTraits<EVMC_BERLIN>>(
        "blake_2f_invalid", "fail-blake2f.json", 0x09_address);
}

TEST(Prague, blsg1add_valid)
{
    do_geth_tests<EvmTraits<EVMC_PRAGUE>>(
        "bls_g1_add_valid", "blsG1Add.json", 0x0b_address);
}

TEST(Prague, blsg1mul_valid)
{
    do_geth_tests<EvmTraits<EVMC_PRAGUE>>(
        "bls_g1_mul_valid", "blsG1Mul.json", 0x0c_address);
}

TEST(Prague, blsg1msm_valid)
{
    do_geth_tests<EvmTraits<EVMC_PRAGUE>>(
        "bls_g1_msm_valid", "blsG1MultiExp.json", 0x0c_address);
}

TEST(Prague, bls_map_g1_valid)
{
    do_geth_tests<EvmTraits<EVMC_PRAGUE>>(
        "bls12_map_fp_to_g1_valid", "blsMapG1.json", 0x10_address);
}

TEST(Prague, blsg2add_valid)
{
    do_geth_tests<EvmTraits<EVMC_PRAGUE>>(
        "bls_g2_add_valid", "blsG2Add.json", 0x0d_address);
}

TEST(Prague, blsg2mul_valid)
{
    do_geth_tests<EvmTraits<EVMC_PRAGUE>>(
        "bls_g2_mul_valid", "blsG2Mul.json", 0x0e_address);
}

TEST(Prague, blsg2msm_valid)
{
    do_geth_tests<EvmTraits<EVMC_PRAGUE>>(
        "bls_g2_msm_valid", "blsG2MultiExp.json", 0x0e_address);
}

TEST(Prague, bls_map_g2_valid)
{
    do_geth_tests<EvmTraits<EVMC_PRAGUE>>(
        "bls12_map_fp2_to_g2_valid", "blsMapG2.json", 0x11_address);
}

TEST(Prague, blsg1add_invalid)
{
    do_geth_tests<EvmTraits<EVMC_PRAGUE>>(
        "bls_g1_add_invalid", "fail-blsG1Add.json", 0x0b_address);
}

TEST(Prague, blsg1mul_invalid)
{
    do_geth_tests<EvmTraits<EVMC_PRAGUE>>(
        "bls_g1_mul_invalid", "fail-blsG1Mul.json", 0x0c_address);
}

TEST(Prague, blsg1msm_invalid)
{
    do_geth_tests<EvmTraits<EVMC_PRAGUE>>(
        "bls_g1_msm_invalid", "fail-blsG1MultiExp.json", 0x0c_address);
}

TEST(Prague, bls_map_g1_invalid)
{
    do_geth_tests<EvmTraits<EVMC_PRAGUE>>(
        "bls12_map_fp_to_g1_valid", "fail-blsMapG1.json", 0x10_address);
}

TEST(Prague, blsg2add_invalid)
{
    do_geth_tests<EvmTraits<EVMC_PRAGUE>>(
        "bls_g2_add_invalid", "fail-blsG2Add.json", 0x0d_address);
}

TEST(Prague, blsg2mul_invalid)
{
    do_geth_tests<EvmTraits<EVMC_PRAGUE>>(
        "bls_g2_mul_invalid", "fail-blsG2Mul.json", 0x0e_address);
}

TEST(Prague, blsg2msm_invalid)
{
    do_geth_tests<EvmTraits<EVMC_PRAGUE>>(
        "bls_g2_msm_invalid", "fail-blsG2MultiExp.json", 0x0e_address);
}

TEST(Prague, bls_map_g2_invalid)
{
    do_geth_tests<EvmTraits<EVMC_PRAGUE>>(
        "bls12_map_fp2_to_g2_valid", "fail-blsMapG2.json", 0x11_address);
}

TEST(Prague, bls_pairing_check_valid)
{
    do_geth_tests<EvmTraits<EVMC_PRAGUE>>(
        "bls12_pairing_check_valid", "blsPairing.json", 0x0f_address);
}

TEST(Prague, bls_pairing_check_invalid)
{
    do_geth_tests<EvmTraits<EVMC_PRAGUE>>(
        "bls12_pairing_check_invalid", "fail-blsPairing.json", 0x0f_address);
}

TEST(Osaka, p256_verify)
{
    do_geth_tests<EvmTraits<EVMC_OSAKA>>(
        "p256_verify", "p256Verify.json", 0x0100_address);
}

TEST(MonadFour, p256_verify)
{
    do_geth_tests<MonadTraits<MONAD_FOUR>>(
        "p256_verify", "p256Verify.json", 0x0100_address);
}

TEST(MonadFour, bn_add)
{
    auto const tests = transform_test_cases(
        load_test_cases(test_resource::geth_vectors_dir / "bn256Add.json"),
        [](auto &test) { test.gas *= 2; });

    do_geth_tests<MonadTraits<MONAD_FOUR>>("bn_add", tests, 0x06_address);
}

TEST(MonadFour, bn_mul)
{
    auto const tests = transform_test_cases(
        load_test_cases(
            test_resource::geth_vectors_dir / "bn256ScalarMul.json"),
        [](auto &test) { test.gas *= 5; });

    do_geth_tests<MonadTraits<MONAD_FOUR>>("bn_mul", tests, 0x07_address);
}

TEST(MonadFour, bn_pairing)
{
    auto const tests = transform_test_cases(
        load_test_cases(test_resource::geth_vectors_dir / "bn256Pairing.json"),
        [](auto &test) { test.gas *= 5; });

    do_geth_tests<MonadTraits<MONAD_FOUR>>("bn_pairing", tests, 0x08_address);
}

TEST(MonadFour, blake2f_valid)
{
    auto const tests = transform_test_cases(
        load_test_cases(test_resource::geth_vectors_dir / "blake2F.json"),
        [](auto &test) { test.gas *= 2; });

    do_geth_tests<MonadTraits<MONAD_FOUR>>(
        "blake_2f_valid", tests, 0x09_address);
}
