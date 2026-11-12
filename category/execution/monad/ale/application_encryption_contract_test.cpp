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
#include <category/execution/ethereum/core/contract/abi_decode_error.hpp>
#include <category/execution/ethereum/core/contract/abi_encode.hpp>
#include <category/execution/ethereum/db/trie_db.hpp>
#include <category/execution/ethereum/db/util.hpp>
#include <category/execution/ethereum/state2/block_state.hpp>
#include <category/execution/ethereum/state3/state.hpp>
#include <category/execution/ethereum/trace/call_tracer.hpp>
#include <category/execution/monad/ale/application_encryption_contract.hpp>
#include <category/execution/monad/ale/application_encryption_error.hpp>
#include <category/mpt/db.hpp>
#include <category/vm/vm.hpp>

#include <gtest/gtest.h>

#include <cstddef>
#include <memory>

using namespace monad;

namespace
{
    constexpr uint64_t DESTINATION_DOMAIN = 0x510000004eaf;

    // Independently computed with cthash: Keccak-256 of these two ABI words,
    // representing the destination domain and the mapping's root slot (7):
    // 0000000000000000000000000000000000000000000000000000510000004eaf
    // 0000000000000000000000000000000000000000000000000000000000000007
    constexpr auto DESTINATION_KEY_SLOT =
        0x7b4e93f8fe9bc472b1fac84156f4243b62a421ce301fbbe4cb12ff9ad4c799aa_bytes32;

    constexpr auto DESTINATION_KEY =
        0x000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f_bytes32;
}

struct ApplicationEncryptionContractTest : public ::testing::Test
{
    vm::VM vm;
    mpt::Db db{std::make_unique<InMemoryMachine>()};
    TrieDb trie_db{db};
    BlockState block_state{trie_db, vm};
    State state{block_state, Incarnation{0, 0}};
    NoopCallTracer call_tracer;
    ApplicationEncryptionContract contract{state, call_tracer};
};

TEST_F(ApplicationEncryptionContractTest, destination_key_rejects_missing_spoke)
{
    auto const result =
        read_destination_key(state, SPOKE_CA, uint256_t{7}, DESTINATION_DOMAIN);
    ASSERT_TRUE(result.has_error());
    EXPECT_EQ(result.assume_error(), ApplicationEncryptionError::SpokeNotFound);
}

TEST_F(ApplicationEncryptionContractTest, destination_key_rejects_missing_key)
{
    state.set_nonce(SPOKE_CA, 1);

    auto const result =
        read_destination_key(state, SPOKE_CA, uint256_t{7}, DESTINATION_DOMAIN);
    ASSERT_TRUE(result.has_error());
    EXPECT_EQ(
        result.assume_error(),
        ApplicationEncryptionError::DestinationKeyNotFound);
}

TEST_F(
    ApplicationEncryptionContractTest,
    destination_key_uses_solidity_mapping_slot)
{
    state.set_nonce(SPOKE_CA, 1);
    state.set_storage(SPOKE_CA, DESTINATION_KEY_SLOT, DESTINATION_KEY);

    auto const result =
        read_destination_key(state, SPOKE_CA, uint256_t{7}, DESTINATION_DOMAIN);
    ASSERT_TRUE(result.has_value());
    EXPECT_EQ(result.value(), DESTINATION_KEY);

    auto const other_domain = read_destination_key(
        state, SPOKE_CA, uint256_t{7}, DESTINATION_DOMAIN + 1);
    ASSERT_TRUE(other_domain.has_error());
    EXPECT_EQ(
        other_domain.assume_error(),
        ApplicationEncryptionError::DestinationKeyNotFound);

    auto const other_slot =
        read_destination_key(state, SPOKE_CA, uint256_t{8}, DESTINATION_DOMAIN);
    ASSERT_TRUE(other_slot.has_error());
    EXPECT_EQ(
        other_slot.assume_error(),
        ApplicationEncryptionError::DestinationKeyNotFound);

    auto const other_spoke_address = Address{0x123456};
    state.set_nonce(other_spoke_address, 1);
    auto const other_spoke = read_destination_key(
        state, other_spoke_address, uint256_t{7}, DESTINATION_DOMAIN);
    ASSERT_TRUE(other_spoke.has_error());
    EXPECT_EQ(
        other_spoke.assume_error(),
        ApplicationEncryptionError::DestinationKeyNotFound);
}

TEST_F(
    ApplicationEncryptionContractTest,
    destination_key_observes_updates_and_rollback)
{
    state.set_nonce(SPOKE_CA, 1);
    state.set_storage(SPOKE_CA, DESTINATION_KEY_SLOT, DESTINATION_KEY);

    state.push();
    state.set_storage(SPOKE_CA, DESTINATION_KEY_SLOT, bytes32_t{0xff});
    auto const changed =
        read_destination_key(state, SPOKE_CA, uint256_t{7}, DESTINATION_DOMAIN);
    ASSERT_TRUE(changed.has_value());
    EXPECT_EQ(changed.value(), bytes32_t{0xff});

    state.pop_reject();
    auto const restored =
        read_destination_key(state, SPOKE_CA, uint256_t{7}, DESTINATION_DOMAIN);
    ASSERT_TRUE(restored.has_value());
    EXPECT_EQ(restored.value(), DESTINATION_KEY);
}

TEST_F(ApplicationEncryptionContractTest, seal_reads_destination_key)
{
    AbiEncoder encoder;
    encoder.add_bytes(byte_string{0xab});
    encoder.add_uint(u64_be{DESTINATION_DOMAIN});
    encoder.add_address(Address{0x1234});
    encoder.add_bytes(byte_string{0xcd});
    auto const input = encoder.encode_final();

    auto const absent_spoke =
        contract.precompile_seal(input, Address{0x4321}, {});
    ASSERT_TRUE(absent_spoke.has_error());
    EXPECT_EQ(
        absent_spoke.assume_error(), ApplicationEncryptionError::SpokeNotFound);

    state.set_nonce(SPOKE_CA, 1);
    auto const absent_key =
        contract.precompile_seal(input, Address{0x4321}, {});
    ASSERT_TRUE(absent_key.has_error());
    EXPECT_EQ(
        absent_key.assume_error(),
        ApplicationEncryptionError::DestinationKeyNotFound);

    state.set_storage(SPOKE_CA, DESTINATION_KEY_SLOT, DESTINATION_KEY);
    auto const installed = contract.precompile_seal(input, Address{0x4321}, {});
    ASSERT_TRUE(installed.has_error());
    // A successful lookup reaches the remaining encryption stub.
    EXPECT_EQ(
        installed.assume_error(), ApplicationEncryptionError::NotImplemented);
}

TEST_F(
    ApplicationEncryptionContractTest,
    seal_message_dispatches_solidity_selector)
{
    AbiEncoder encoder;
    encoder.add_uint(u64_be{DESTINATION_DOMAIN});
    encoder.add_uint(u256_be{uint256_t{1} << 200});
    encoder.add_bytes(byte_string{0xab});
    auto const arguments = encoder.encode_final();

    byte_string input{0x57, 0x60, 0xb0, 0x4f};
    input += arguments;
    byte_string_view remaining{input};
    auto const [method, cost] =
        ApplicationEncryptionContract::precompile_dispatch<
            MonadTraits<MONAD_NEXT>>(remaining);

    EXPECT_EQ(method, &ApplicationEncryptionContract::precompile_seal_message);
    EXPECT_EQ(cost, 100);
    EXPECT_EQ(remaining, byte_string_view{arguments});
}

TEST_F(
    ApplicationEncryptionContractTest, seal_message_decodes_dynamic_plaintext)
{
    state.set_nonce(SPOKE_CA, 1);
    state.set_storage(SPOKE_CA, DESTINATION_KEY_SLOT, DESTINATION_KEY);

    for (size_t const size : {0uz, 1uz, 31uz, 32uz, 33uz, 65uz}) {
        SCOPED_TRACE(size);
        AbiEncoder encoder;
        encoder.add_uint(u64_be{DESTINATION_DOMAIN});
        encoder.add_uint(u256_be{uint256_t{1} << 200});
        encoder.add_bytes(byte_string(size, 0xab));
        auto const input = encoder.encode_final();

        auto const result =
            contract.precompile_seal_message(input, SPOKE_CA, {});
        ASSERT_TRUE(result.has_error());
        EXPECT_EQ(
            result.assume_error(), ApplicationEncryptionError::NotImplemented);
    }
}

TEST_F(
    ApplicationEncryptionContractTest, seal_message_rejects_truncated_arguments)
{
    AbiEncoder encoder;
    encoder.add_uint(u64_be{DESTINATION_DOMAIN});
    encoder.add_uint(u256_be{uint256_t{1} << 200});
    encoder.add_bytes(byte_string(33, 0xab));
    auto const encoded = encoder.encode_final();

    for (size_t size = 0; size < encoded.size(); ++size) {
        SCOPED_TRACE(size);
        auto const input = byte_string_view{encoded}.substr(0, size);
        auto const result =
            contract.precompile_seal_message(input, SPOKE_CA, {});
        ASSERT_TRUE(result.has_error());
        EXPECT_EQ(result.assume_error(), AbiDecodeError::InputTooShort);
    }
}

TEST_F(ApplicationEncryptionContractTest, seal_message_rejects_nonzero_value)
{
    auto const result =
        contract.precompile_seal_message({}, SPOKE_CA, bytes32_t{1});
    ASSERT_TRUE(result.has_error());
    EXPECT_EQ(result.assume_error(), ApplicationEncryptionError::ValueNonZero);
}

TEST_F(ApplicationEncryptionContractTest, seal_message_reads_destination_key)
{
    AbiEncoder encoder;
    encoder.add_uint(u64_be{DESTINATION_DOMAIN});
    encoder.add_uint(u256_be{uint256_t{1} << 200});
    encoder.add_bytes(byte_string{0xab});
    auto const input = encoder.encode_final();

    auto const absent_spoke =
        contract.precompile_seal_message(input, SPOKE_CA, {});
    ASSERT_TRUE(absent_spoke.has_error());
    EXPECT_EQ(
        absent_spoke.assume_error(), ApplicationEncryptionError::SpokeNotFound);

    state.set_nonce(SPOKE_CA, 1);
    auto const absent_key =
        contract.precompile_seal_message(input, SPOKE_CA, {});
    ASSERT_TRUE(absent_key.has_error());
    EXPECT_EQ(
        absent_key.assume_error(),
        ApplicationEncryptionError::DestinationKeyNotFound);

    state.set_storage(SPOKE_CA, DESTINATION_KEY_SLOT, DESTINATION_KEY);
    auto const installed =
        contract.precompile_seal_message(input, SPOKE_CA, {});
    ASSERT_TRUE(installed.has_error());
    EXPECT_EQ(
        installed.assume_error(), ApplicationEncryptionError::NotImplemented);
}

TEST_F(ApplicationEncryptionContractTest, unseal_decodes_dynamic_arguments)
{
    for (auto const &[blob_size, ctx_size] : {
             std::pair{0uz, 0uz},
             std::pair{33uz, 1uz},
             std::pair{1uz, 33uz},
             std::pair{33uz, 65uz},
         }) {
        SCOPED_TRACE(blob_size);
        SCOPED_TRACE(ctx_size);
        AbiEncoder encoder;
        encoder.add_bytes(byte_string(blob_size, 0xAB));
        encoder.add_bytes(byte_string(ctx_size, 0xCD));
        auto const input = encoder.encode_final();

        auto const result = contract.precompile_unseal(input, Address{}, {});
        ASSERT_TRUE(result.has_error());
        EXPECT_EQ(
            result.assume_error(), ApplicationEncryptionError::NotImplemented);
    }
}

TEST_F(ApplicationEncryptionContractTest, unseal_rejects_truncated_arguments)
{
    AbiEncoder encoder;
    encoder.add_bytes(byte_string(33, 0xAB));
    encoder.add_bytes(byte_string(65, 0xCD));
    auto const encoded = encoder.encode_final();

    for (size_t size = 0; size < encoded.size(); ++size) {
        SCOPED_TRACE(size);
        auto const input = byte_string_view{encoded}.substr(0, size);
        auto const result = contract.precompile_unseal(input, Address{}, {});
        ASSERT_TRUE(result.has_error());
        EXPECT_EQ(result.assume_error(), AbiDecodeError::InputTooShort);
    }
}

TEST(ApplicationEncryptionAd, binary_context_spans_two_words)
{
    auto const app_ctx = from_hex(
                             "000102030405060708090a0b0c0d0e0f10111213141516171"
                             "8191a1b1c1d1e1f20")
                             .value();
    // Independently encoded from the ABI tuple layout in Python. Each literal
    // below is one word; the label excludes its terminating null byte.
    auto const expected =
        from_hex(
            "0000000000000000000000000000000000000000000000000000000000000080"
            "0000000000000000000000000000000000000000000000000000510000004eaf"
            "0000000000000000000000000123456789abcdef0123456789abcdef01234567"
            "00000000000000000000000000000000000000000000000000000000000000c0"
            "0000000000000000000000000000000000000000000000000000000000000014"
            "6d6f6e61642d7365616c65642d626c6f622d7631000000000000000000000000"
            "0000000000000000000000000000000000000000000000000000000000000021"
            "000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f"
            "2000000000000000000000000000000000000000000000000000000000000000")
            .value();

    EXPECT_EQ(
        sealed_blob_ad(
            0x510000004eaf,
            0x0123456789abcdef0123456789abcdef01234567_address,
            app_ctx),
        expected);
}

TEST(ApplicationEncryptionAd, empty_context)
{
    auto const expected =
        from_hex(
            "0000000000000000000000000000000000000000000000000000000000000080"
            "0000000000000000000000000000000000000000000000000000510000004eaf"
            "0000000000000000000000000123456789abcdef0123456789abcdef01234567"
            "00000000000000000000000000000000000000000000000000000000000000c0"
            "0000000000000000000000000000000000000000000000000000000000000014"
            "6d6f6e61642d7365616c65642d626c6f622d7631000000000000000000000000"
            "0000000000000000000000000000000000000000000000000000000000000000")
            .value();

    EXPECT_EQ(
        sealed_blob_ad(
            0x510000004eaf,
            0x0123456789abcdef0123456789abcdef01234567_address,
            {}),
        expected);
}
