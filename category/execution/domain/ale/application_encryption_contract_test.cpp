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

#include <category/core/assert.h>
#include <category/core/hex.hpp>
#include <category/execution/domain/ale/application_encryption_contract.hpp>
#include <category/execution/domain/ale/application_encryption_error.hpp>
#include <category/execution/domain/hpke.hpp>
#include <category/execution/ethereum/block_hash_buffer.hpp>
#include <category/execution/ethereum/core/contract/abi_decode_error.hpp>
#include <category/execution/ethereum/core/contract/abi_encode.hpp>
#include <category/execution/ethereum/db/trie_db.hpp>
#include <category/execution/ethereum/db/util.hpp>
#include <category/execution/ethereum/precompiles.hpp>
#include <category/execution/ethereum/state2/block_state.hpp>
#include <category/execution/ethereum/state3/state.hpp>
#include <category/execution/ethereum/state_host.hpp>
#include <category/execution/ethereum/trace/call_tracer.hpp>
#include <category/execution/ethereum/tx_context.hpp>
#include <category/execution/monad/chain/monad_chain.hpp>
#include <category/execution/monad/reserve_balance/reserve_balance_contract.hpp>
#include <category/execution/monad/staking/util/constants.hpp>
#include <category/mpt/db.hpp>
#include <category/vm/vm.hpp>

#include <gtest/gtest.h>
#include <nlohmann/json.hpp>

#include <cstddef>
#include <cstdlib>
#include <filesystem>
#include <fstream>
#include <memory>
#include <optional>
#include <string>
#include <string_view>
#include <unistd.h>
#include <utility>
#include <vector>

using namespace monad;

namespace
{
    constexpr uint64_t SOURCE_DOMAIN = 0x520000004eaf;
    constexpr uint64_t DESTINATION_DOMAIN = 0x510000004eaf;
    constexpr Address SPOKE_CA{0x12345678};
    constexpr auto TX_ORIGIN =
        0x89abcdef0123456789abcdef0123456789abcdef_address;
    constexpr uint64_t TX_NONCE = 0xfedcba9876543210;

    domain::PrivateDomainKey load_test_key()
    {
        std::string path = "/tmp/monad-ale-key-XXXXXX";
        int const fd = ::mkstemp(path.data());
        MONAD_ASSERT(fd != -1);
        ::close(fd);
        {
            std::ofstream stream{path, std::ios::binary};
            stream << R"(-----BEGIN PRIVATE KEY-----
MC4CAQAwBQYDK2VuBCIEIBERERERERERERERERERERERERERERERERERERERERER
-----END PRIVATE KEY-----
)";
            EXPECT_TRUE(stream.good());
        }
        auto key = domain::PrivateDomainKey::load(path);
        std::filesystem::remove(path);
        return std::move(key).value();
    }

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
    domain::PrivateDomainKey const key = load_test_key();
    ApplicationEncryptionContext const encryption_context{
        SOURCE_DOMAIN, key, SPOKE_CA};
    ApplicationEncryptionContract contract{
        state, call_tracer, encryption_context, TX_ORIGIN, TX_NONCE};

    static uint256_t seal_index(State &current_state)
    {
        return load_be<uint256_t>(current_state.get_transient_storage(
            ALE_CA, ApplicationEncryptionContract::SEAL_INDEX_SLOT));
    }

    byte_string seal_input()
    {
        AbiEncoder encoder;
        encoder.add_bytes(byte_string{0xab});
        encoder.add_uint(u64_be{DESTINATION_DOMAIN});
        encoder.add_address(Address{0x1234});
        encoder.add_bytes(byte_string{0xcd});
        return encoder.encode_final();
    }

    void seal(
        ApplicationEncryptionContract &target,
        Address const &sender = Address{1})
    {
        auto const result = target.precompile_seal(seal_input(), sender, {});
        ASSERT_TRUE(result.has_error());
        EXPECT_EQ(
            result.assume_error(), ApplicationEncryptionError::NotImplemented);
    }
};

TEST(ApplicationEncryptionPrecompile, domain_availability)
{
    using traits = MonadTraits<MONAD_NEXT>;
    EXPECT_TRUE(is_precompile<traits>(Address{1}));
    EXPECT_TRUE(is_precompile<traits>(ALE_CA));
    EXPECT_FALSE(is_precompile<traits>(staking::STAKING_CA));
    EXPECT_FALSE(is_precompile<traits>(RESERVE_BALANCE_CA));
    EXPECT_FALSE(is_precompile<traits>(Address{0x1234}));
    EXPECT_FALSE(is_precompile<MonadTraits<MONAD_TEN>>(ALE_CA));
    EXPECT_FALSE(is_precompile<MonadTraits<MONAD_THREE>>(staking::STAKING_CA));
}

TEST_F(ApplicationEncryptionContractTest, domain_host_warming)
{
    using traits = MonadTraits<MONAD_NEXT>;
    auto chain_ctx = ChainContext<traits>::debug_empty();
    chain_ctx.private_domain = true;
    chain_ctx.encryption_context = &encryption_context;
    BlockHashBufferFinalized const block_hashes;
    Transaction const tx{};
    trace::StateTracer state_tracer{std::monostate{}};
    StateHost<traits> host{
        call_tracer,
        state_tracer,
        EMPTY_TX_CONTEXT,
        block_hashes,
        state,
        tx,
        std::nullopt,
        0,
        chain_ctx};
    EXPECT_EQ(host.access_account(Address{1}), AccessStatus::Warm);
    EXPECT_EQ(host.access_account(ALE_CA), AccessStatus::Warm);
    EXPECT_EQ(host.access_account(staking::STAKING_CA), AccessStatus::Cold);
    EXPECT_EQ(host.access_account(RESERVE_BALANCE_CA), AccessStatus::Cold);
    EXPECT_EQ(host.access_account(staking::STAKING_CA), AccessStatus::Warm);
    EXPECT_EQ(host.access_account(RESERVE_BALANCE_CA), AccessStatus::Warm);
}

TEST_F(ApplicationEncryptionContractTest, domain_access_list)
{
    using traits = MonadTraits<MONAD_NEXT>;
    for (auto const address :
         {Address{1}, ALE_CA, staking::STAKING_CA, RESERVE_BALANCE_CA}) {
        (void)state.access_account(address);
    }
    nlohmann::json output;
    std::vector<std::optional<Address>> const authorities;
    trace::AccessListTracer tracer{
        output, Address{}, Address{}, std::nullopt, authorities};
    tracer.encode<traits>(state);
    std::vector<Address> addresses;
    for (auto const &entry : output) {
        addresses.push_back(
            *from_hex<Address>(entry["address"].get<std::string>()));
    }
    EXPECT_EQ(
        addresses,
        (std::vector<Address>{staking::STAKING_CA, RESERVE_BALANCE_CA}));
}

TEST_F(
    ApplicationEncryptionContractTest,
    domain_dispatch_excludes_public_contracts)
{
    using traits = MonadTraits<MONAD_NEXT>;
    for (auto const address : {staking::STAKING_CA, RESERVE_BALANCE_CA}) {
        vm::Message const msg{.code_address = address};
        EXPECT_FALSE(
            check_call_precompile<traits>(state, call_tracer, msg, false)
                .has_value());
    }
}

TEST_F(
    ApplicationEncryptionContractTest,
    dispatch_checks_context_and_rolls_back_seal_index)
{
    using traits = MonadTraits<MONAD_NEXT>;
    state.set_nonce(SPOKE_CA, 1);
    state.set_storage(SPOKE_CA, DESTINATION_KEY_SLOT, DESTINATION_KEY);
    byte_string const input =
        byte_string{0x60, 0x7c, 0x42, 0xc9} + seal_input();
    vm::Message const msg{
        .kind = vm::CallKind::Call,
        .gas = 1'000,
        .recipient = ALE_CA,
        .sender = Address{0x4321},
        .input_data = input.data(),
        .input_size = input.size(),
        .code_address = ALE_CA};

    auto const missing_context =
        check_call_precompile<traits>(state, call_tracer, msg, false);
    ASSERT_TRUE(missing_context.has_value());
    EXPECT_EQ(missing_context->status_code, CallStatus::Rejected);

    auto unrelated_msg = msg;
    unrelated_msg.recipient = Address{0x1234};
    unrelated_msg.code_address = unrelated_msg.recipient;
    EXPECT_FALSE(
        check_call_precompile<traits>(state, call_tracer, unrelated_msg, false)
            .has_value());
    EXPECT_FALSE(check_call_precompile<MonadTraits<MONAD_TEN>>(
                     state, call_tracer, msg, false)
                     .has_value());

    auto chain_ctx = ChainContext<traits>::debug_empty();
    chain_ctx.private_domain = true;
    auto const missing_encryption_context = check_call_precompile<traits>(
        state, call_tracer, msg, false, &chain_ctx);
    ASSERT_TRUE(missing_encryption_context.has_value());
    EXPECT_EQ(missing_encryption_context->status_code, CallStatus::Rejected);

    chain_ctx.encryption_context = &encryption_context;
    chain_ctx.private_domain = false;
    auto const public_context = check_call_precompile<traits>(
        state, call_tracer, msg, false, &chain_ctx);
    ASSERT_TRUE(public_context.has_value());
    EXPECT_EQ(public_context->status_code, CallStatus::Rejected);

    chain_ctx.private_domain = true;
    BlockHashBufferFinalized const block_hashes;
    auto tx_context = EMPTY_TX_CONTEXT;
    tx_context.tx_origin = TX_ORIGIN;
    Transaction const tx{.nonce = TX_NONCE};
    auto const missing_tx_context = check_call_precompile<traits>(
        state, call_tracer, msg, false, &chain_ctx, nullptr, &tx);
    ASSERT_TRUE(missing_tx_context.has_value());
    EXPECT_EQ(missing_tx_context->status_code, CallStatus::Rejected);
    auto const missing_transaction = check_call_precompile<traits>(
        state, call_tracer, msg, false, &chain_ctx, &tx_context);
    ASSERT_TRUE(missing_transaction.has_value());
    EXPECT_EQ(missing_transaction->status_code, CallStatus::Rejected);

    trace::StateTracer state_tracer{std::monostate{}};
    StateHost<traits> host{
        call_tracer,
        state_tracer,
        tx_context,
        block_hashes,
        state,
        tx,
        std::nullopt,
        0,
        chain_ctx};
    state.set_transient_storage(
        ALE_CA, ApplicationEncryptionContract::SEAL_INDEX_SLOT, bytes32_t{7});
    auto const result = execute_call_message<traits>(&host, state, msg);
    EXPECT_EQ(result.status_code, CallStatus::Revert);
    EXPECT_EQ(
        (std::string_view{
            reinterpret_cast<char const *>(result.output_data),
            result.output_size}),
        "application encryption is not implemented");
    EXPECT_EQ(seal_index(state), 7);
}

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
    auto const input = seal_input();

    auto const absent_spoke =
        contract.precompile_seal(input, Address{0x4321}, {});
    ASSERT_TRUE(absent_spoke.has_error());
    EXPECT_EQ(
        absent_spoke.assume_error(), ApplicationEncryptionError::SpokeNotFound);
    EXPECT_EQ(seal_index(state), 0);

    state.set_nonce(SPOKE_CA, 1);
    auto const absent_key =
        contract.precompile_seal(input, Address{0x4321}, {});
    ASSERT_TRUE(absent_key.has_error());
    EXPECT_EQ(
        absent_key.assume_error(),
        ApplicationEncryptionError::DestinationKeyNotFound);
    EXPECT_EQ(seal_index(state), 0);

    state.set_storage(SPOKE_CA, DESTINATION_KEY_SLOT, DESTINATION_KEY);
    auto const installed = contract.precompile_seal(input, Address{0x4321}, {});
    ASSERT_TRUE(installed.has_error());
    // A successful lookup reaches the remaining encryption stub.
    EXPECT_EQ(
        installed.assume_error(), ApplicationEncryptionError::NotImplemented);
    EXPECT_EQ(seal_index(state), 1);
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

TEST(ApplicationEncryptionRandomnessInput, binary_fields_match_abi_fixture)
{
    auto const blob =
        from_hex("000102030405060708090a0b0c0d0e0f101112131415161718"
                 "191a1b1c1d1e1f20")
            .value();
    // Independently encoded in Python from the eight-word ABI head and
    // length-prefixed tails. The nonce and index exceed uint32_t; the blob
    // spans two words and the public key contains a leading zero byte.
    auto const expected =
        from_hex(
            "0000000000000000000000000000000000000000000000000000000000000100"
            "00000000000000000000000089abcdef0123456789abcdef0123456789abcdef"
            "000000000000000000000000000000000000000000000000fedcba9876543210"
            "0000000000000000000000000000000000000000000000000000000100000007"
            "0000000000000000000000000123456789abcdef0123456789abcdef01234567"
            "0000000000000000000000000000000000000000000000000000000000000140"
            "0000000000000000000000000000000000000000000000000000000000000180"
            "00000000000000000000000000000000000000000000000000000000000001c0"
            "000000000000000000000000000000000000000000000000000000000000001e"
            "6d6f6e61642d707265636f6d70696c652d72616e646f6d6e6573732d76310000"
            "0000000000000000000000000000000000000000000000000000000000000020"
            "000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f"
            "0000000000000000000000000000000000000000000000000000000000000002"
            "0102000000000000000000000000000000000000000000000000000000000000"
            "0000000000000000000000000000000000000000000000000000000000000021"
            "000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f"
            "2000000000000000000000000000000000000000000000000000000000000000")
            .value();

    EXPECT_EQ(
        sealed_blob_randomness_input(
            TX_ORIGIN,
            TX_NONCE,
            0x100000007,
            0x0123456789abcdef0123456789abcdef01234567_address,
            DESTINATION_KEY,
            byte_string{0x01, 0x02},
            blob),
        expected);
}

TEST(ApplicationEncryptionRandomnessInput, separates_dynamic_fields)
{
    // The same concatenated AD and plaintext must encode differently when
    // their boundary changes, including when one field becomes empty.
    auto const first = sealed_blob_randomness_input(
        TX_ORIGIN,
        TX_NONCE,
        0,
        Address{1},
        DESTINATION_KEY,
        byte_string{0x01},
        byte_string{0x02});
    auto const second = sealed_blob_randomness_input(
        TX_ORIGIN,
        TX_NONCE,
        0,
        Address{1},
        DESTINATION_KEY,
        byte_string{0x01, 0x02},
        {});

    EXPECT_NE(first, second);
}

TEST_F(
    ApplicationEncryptionContractTest,
    seal_index_restores_parent_value_on_revert)
{
    state.set_nonce(SPOKE_CA, 1);
    state.set_storage(SPOKE_CA, DESTINATION_KEY_SLOT, DESTINATION_KEY);
    state.push();
    seal(contract);
    EXPECT_EQ(seal_index(state), 1);

    state.push();
    seal(contract);
    seal(contract);
    EXPECT_EQ(seal_index(state), 3);
    state.pop_reject();

    EXPECT_EQ(seal_index(state), 1);
    seal(contract);
    state.pop_accept();
    EXPECT_EQ(seal_index(state), 2);
}

TEST_F(
    ApplicationEncryptionContractTest,
    seal_index_parent_revert_undoes_accepted_child)
{
    state.set_nonce(SPOKE_CA, 1);
    state.set_storage(SPOKE_CA, DESTINATION_KEY_SLOT, DESTINATION_KEY);
    state.push();
    seal(contract);
    state.push();
    seal(contract);
    state.pop_accept();
    EXPECT_EQ(seal_index(state), 2);

    state.pop_reject();
    EXPECT_EQ(seal_index(state), 0);
}

TEST_F(
    ApplicationEncryptionContractTest, seal_index_is_local_to_each_transaction)
{
    State setup{block_state, Incarnation{0, 0}};
    setup.set_nonce(SPOKE_CA, 1);
    setup.set_storage(SPOKE_CA, DESTINATION_KEY_SLOT, DESTINATION_KEY);
    block_state.merge(setup);

    State other{block_state, Incarnation{0, 1}};
    ApplicationEncryptionContract other_contract{
        other, call_tracer, encryption_context, TX_ORIGIN, TX_NONCE + 1};
    EXPECT_EQ(seal_index(state), 0);
    EXPECT_EQ(seal_index(other), 0);

    seal(contract);
    seal(other_contract);
    seal(contract);
    EXPECT_EQ(seal_index(state), 2);
    EXPECT_EQ(seal_index(other), 1);

    ASSERT_TRUE(block_state.can_merge(state));
    block_state.merge(state);
    ASSERT_TRUE(block_state.can_merge(other));
    block_state.merge(other);

    State next{block_state, Incarnation{0, 2}};
    EXPECT_EQ(seal_index(next), 0);
    EXPECT_EQ(seal_index(state), 2);
    EXPECT_EQ(seal_index(other), 1);
}

TEST_F(
    ApplicationEncryptionContractTest,
    seal_index_is_shared_by_contract_instances)
{
    state.set_nonce(SPOKE_CA, 1);
    state.set_storage(SPOKE_CA, DESTINATION_KEY_SLOT, DESTINATION_KEY);
    seal(contract);
    EXPECT_EQ(seal_index(state), 1);

    ApplicationEncryptionContract another{
        state, call_tracer, encryption_context, TX_ORIGIN, TX_NONCE};
    seal(another, Address{2});
    EXPECT_EQ(seal_index(state), 2);
}

TEST(ApplicationEncryptionAd, binary_context_spans_two_words)
{
    auto const app_ctx =
        from_hex("000102030405060708090a0b0c0d0e0f10111213141516171"
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
