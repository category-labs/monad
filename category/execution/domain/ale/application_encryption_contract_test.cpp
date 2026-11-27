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
#include <category/core/hex.hpp>
#include <category/core/int.hpp>
#include <category/core/runtime/uint256.hpp>
#include <category/execution/domain/ale/application_encryption_contract.hpp>
#include <category/execution/domain/ale/application_encryption_error.hpp>
#include <category/execution/domain/hpke.hpp>
#include <category/execution/ethereum/block_hash_buffer.hpp>
#include <category/execution/ethereum/core/contract/abi_decode.hpp>
#include <category/execution/ethereum/core/contract/abi_decode_error.hpp>
#include <category/execution/ethereum/core/contract/abi_encode.hpp>
#include <category/execution/ethereum/db/trie_db.hpp>
#include <category/execution/ethereum/db/util.hpp>
#include <category/execution/ethereum/precompiles.hpp>
#include <category/execution/ethereum/state2/block_state.hpp>
#include <category/execution/ethereum/state3/state.hpp>
#include <category/execution/ethereum/state_host.hpp>
#include <category/execution/ethereum/trace/call_tracer.hpp>
#include <category/execution/ethereum/trace/state_tracer.hpp>
#include <category/execution/ethereum/tx_context.hpp>
#include <category/execution/monad/chain/monad_chain.hpp>
#include <category/execution/monad/reserve_balance/reserve_balance_contract.hpp>
#include <category/execution/monad/staking/util/constants.hpp>
#include <category/mpt/db.hpp>
#include <category/vm/evm/access_status.hpp>
#include <category/vm/evm/call_status.hpp>
#include <category/vm/evm/message.hpp>
#include <category/vm/evm/monad/revision.h>
#include <category/vm/evm/opcodes.hpp>
#include <category/vm/evm/result.hpp>
#include <category/vm/evm/traits.hpp>
#include <category/vm/vm.hpp>

#include <gtest/gtest.h>
#include <nlohmann/json.hpp>

#include <cstddef>
#include <cstdint>
#include <filesystem>
#include <fstream>
#include <ios>
#include <memory>
#include <optional>
#include <stdlib.h>
#include <string>
#include <string_view>
#include <unistd.h>
#include <utility>
#include <variant>
#include <vector>

using namespace monad;

namespace
{
    constexpr uint64_t SOURCE_DOMAIN = 0x520000004eaf;
    constexpr uint64_t DESTINATION_DOMAIN = 0x510000004eaf;
    constexpr Address SPOKE_CA{0x12345678};
    constexpr Address MESSAGE_FROM{0x4321};
    constexpr Address MESSAGE_TO{0x1234};
    constexpr uint256_t MESSAGE_SEQUENCE = (uint256_t{1} << 200) | 7;
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

    // Public key for the raw X25519 private key 0x22 * 32.
    constexpr auto RECIPIENT_KEY =
        0x0faa684ed28867b97f4a6a2dee5df8ce974e76b7018e3f22a1c4cf2678570f20_bytes32;
}

struct ApplicationEncryptionContractTest : public ::testing::Test
{
    using traits = MonadTraits<MONAD_NEXT>;
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
        state, call_tracer, encryption_context, TX_ORIGIN, TX_NONCE, 0};

    ChainContext<traits> chain_ctx = ChainContext<traits>::debug_empty();
    BlockHashBufferFinalized const block_hashes;
    vm::TxContext const tx_context = [] {
        auto context = EMPTY_TX_CONTEXT;
        context.tx_origin = TX_ORIGIN;
        return context;
    }();
    Transaction const tx{.nonce = TX_NONCE};
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

    explicit ApplicationEncryptionContractTest(
        vm::VM::Mode const mode = vm::VM::Dual)
        : vm{mode}
    {
        chain_ctx.private_domain = true;
        chain_ctx.encryption_context = &encryption_context;
    }

    byte_string seal_input(
        byte_string_view const blob = byte_string{0xab},
        byte_string_view const app_ctx = byte_string{0xcd})
    {
        AbiEncoder encoder;
        encoder.add_bytes(blob);
        encoder.add_uint(u64_be{DESTINATION_DOMAIN});
        encoder.add_address(Address{0x1234});
        encoder.add_bytes(app_ctx);
        return encoder.encode_final();
    }

    byte_string seal_calldata()
    {
        return byte_string{0x60, 0x7c, 0x42, 0xc9} + seal_input();
    }

    static byte_string message_plaintext(byte_string_view const body)
    {
        AbiEncoder encoder;
        encoder.add_address(MESSAGE_FROM);
        encoder.add_address(MESSAGE_TO);
        encoder.add_bytes(body);
        return encoder.encode_final();
    }

    static byte_string seal_message_input(byte_string_view const plaintext)
    {
        AbiEncoder encoder;
        encoder.add_uint(u64_be{DESTINATION_DOMAIN});
        encoder.add_uint(u256_be{MESSAGE_SEQUENCE});
        encoder.add_bytes(plaintext);
        return encoder.encode_final();
    }

    static vm::Message seal_call(
        byte_string_view const input, Address const &sender = Address{0x4321})
    {
        return {
            .kind = vm::CallKind::Call,
            .depth = 1,
            .gas = 1'000,
            .recipient = ALE_CA,
            .sender = sender,
            .input_data = input.data(),
            .input_size = input.size(),
            .code_address = ALE_CA};
    }

    vm::Result execute_seal()
    {
        auto const input = seal_calldata();
        return execute_message(seal_call(input));
    }

    vm::Result execute_seal_message(
        byte_string_view const plaintext, Address const &sender = SPOKE_CA)
    {
        auto const input =
            byte_string{0x57, 0x60, 0xb0, 0x4f} + seal_message_input(plaintext);
        return execute_message(seal_call(input, sender));
    }

    vm::Result execute_message(vm::Message message)
    {
        return execute_message(message, host);
    }

    vm::Result
    execute_message(vm::Message message, StateHost<traits> &execution_host)
    {
        auto memory = vm.message_memory_ref();
        message.memory_handle = memory.get();
        message.memory = memory.get();
        message.memory_capacity = vm.message_memory_capacity();
        return execution_host.call(message);
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
            check_call_precompile<traits>(state, call_tracer, msg, false, 0)
                .has_value());
    }
}

TEST_F(
    ApplicationEncryptionContractTest,
    dispatch_requires_domain_and_transaction_context)
{
    using traits = MonadTraits<MONAD_NEXT>;
    auto const input = seal_calldata();
    auto const msg = seal_call(input);

    auto const missing_context =
        check_call_precompile<traits>(state, call_tracer, msg, false, 0);
    ASSERT_TRUE(missing_context.has_value());
    EXPECT_EQ(missing_context->status_code, CallStatus::Rejected);

    auto unrelated_msg = msg;
    unrelated_msg.recipient = Address{0x1234};
    unrelated_msg.code_address = unrelated_msg.recipient;
    EXPECT_FALSE(check_call_precompile<traits>(
                     state, call_tracer, unrelated_msg, false, 0)
                     .has_value());
    EXPECT_FALSE(check_call_precompile<MonadTraits<MONAD_TEN>>(
                     state, call_tracer, msg, false, 0)
                     .has_value());

    auto chain_ctx = ChainContext<traits>::debug_empty();
    chain_ctx.private_domain = true;
    auto const missing_encryption_context = check_call_precompile<traits>(
        state, call_tracer, msg, false, 0, &chain_ctx);
    ASSERT_TRUE(missing_encryption_context.has_value());
    EXPECT_EQ(missing_encryption_context->status_code, CallStatus::Rejected);

    chain_ctx.encryption_context = &encryption_context;
    chain_ctx.private_domain = false;
    auto const public_context = check_call_precompile<traits>(
        state, call_tracer, msg, false, 0, &chain_ctx);
    ASSERT_TRUE(public_context.has_value());
    EXPECT_EQ(public_context->status_code, CallStatus::Rejected);

    chain_ctx.private_domain = true;
    auto tx_context = EMPTY_TX_CONTEXT;
    tx_context.tx_origin = TX_ORIGIN;
    Transaction const tx{.nonce = TX_NONCE};
    auto const missing_tx_context = check_call_precompile<traits>(
        state, call_tracer, msg, false, 0, &chain_ctx, nullptr, &tx);
    ASSERT_TRUE(missing_tx_context.has_value());
    EXPECT_EQ(missing_tx_context->status_code, CallStatus::Rejected);
    auto const missing_transaction = check_call_precompile<traits>(
        state, call_tracer, msg, false, 0, &chain_ctx, &tx_context);
    ASSERT_TRUE(missing_transaction.has_value());
    EXPECT_EQ(missing_transaction->status_code, CallStatus::Rejected);
}

TEST_F(
    ApplicationEncryptionContractTest,
    dispatch_seal_matches_independent_ciphertext_vector)
{
    state.set_nonce(SPOKE_CA, 1);
    state.set_storage(SPOKE_CA, DESTINATION_KEY_SLOT, DESTINATION_KEY);
    host.call_sequence_ = 6;
    auto const result = execute_seal();
    ASSERT_EQ(result.status_code, CallStatus::Success);
    EXPECT_EQ(host.call_sequence_, 7);
    EXPECT_EQ(result.gas_left, 900);
    EXPECT_EQ(result.gas_refund, 0);

    // Python cryptography 50.0.2, RFC 9180 labeled HKDF and independently
    // encoded ABI inputs: private key 0x11 * 32, TX_ORIGIN, TX_NONCE, call
    // sequence 7, caller 0x4321, DESTINATION_KEY, destination 0x510000004eaf,
    // recipient 0x1234, app context 0xcd and plaintext 0xab. The return is ABI
    // bytes.
    auto const expected =
        from_hex(
            "0000000000000000000000000000000000000000000000000000000000000020"
            "0000000000000000000000000000000000000000000000000000000000000031"
            "c01aa8e09b4db03f5956ff9b8803eef6da11382f020db816637b5f0b343ef252"
            "596eee1d791f07e68fd9761fa563356368000000000000000000000000000000")
            .value();
    EXPECT_EQ(
        (byte_string_view{result.output_data, result.output_size}), expected);
}

TEST_F(
    ApplicationEncryptionContractTest,
    dispatch_seal_failure_retains_call_sequence)
{
    state.set_nonce(SPOKE_CA, 1);
    // This nonzero low-order point passes the registry lookup but HPKE
    // rejects it because X25519 produces an all-zero shared secret.
    bytes32_t low_order_key{};
    low_order_key.bytes[0] = 1;
    state.set_storage(SPOKE_CA, DESTINATION_KEY_SLOT, low_order_key);
    host.call_sequence_ = 6;
    auto const result = execute_seal();
    EXPECT_EQ(result.status_code, CallStatus::Revert);
    EXPECT_EQ(result.gas_left, 0);
    EXPECT_EQ(host.call_sequence_, 7);
    EXPECT_EQ(
        (std::string_view{
            reinterpret_cast<char const *>(result.output_data),
            result.output_size}),
        "application encryption failed");
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

    state.set_nonce(SPOKE_CA, 1);
    auto const absent_key =
        contract.precompile_seal(input, Address{0x4321}, {});
    ASSERT_TRUE(absent_key.has_error());
    EXPECT_EQ(
        absent_key.assume_error(),
        ApplicationEncryptionError::DestinationKeyNotFound);

    state.set_storage(SPOKE_CA, DESTINATION_KEY_SLOT, DESTINATION_KEY);
    auto const installed = contract.precompile_seal(input, Address{0x4321}, {});
    ASSERT_TRUE(installed.has_value());
}

TEST_F(ApplicationEncryptionContractTest, seal_encrypts_dynamic_arguments)
{
    state.set_nonce(SPOKE_CA, 1);
    state.set_storage(SPOKE_CA, DESTINATION_KEY_SLOT, RECIPIENT_KEY);

    for (auto const &[blob_size, ctx_size] : {
             std::pair{0uz, 0uz},
             std::pair{1uz, 1uz},
             std::pair{31uz, 32uz},
             std::pair{32uz, 31uz},
             std::pair{33uz, 65uz},
             std::pair{65uz, 33uz},
         }) {
        SCOPED_TRACE(blob_size);
        SCOPED_TRACE(ctx_size);
        byte_string const blob(blob_size, 0xab);
        byte_string const app_ctx(ctx_size, 0xcd);
        auto const result = contract.precompile_seal(
            seal_input(blob, app_ctx), Address{0x4321}, {});
        ASSERT_TRUE(result.has_value());

        byte_string_view output = result.value();
        auto const offset = abi_decode_fixed<u256_be>(output);
        ASSERT_TRUE(offset.has_value());
        EXPECT_EQ(offset.value().native(), 32);
        auto const decoded = abi_decode_dynamic_bytes_tail(output);
        ASSERT_TRUE(decoded.has_value());
        EXPECT_TRUE(output.empty());
        auto const payload = decoded.value();
        ASSERT_EQ(payload.size(), blob.size() + 32 + 16);

        auto const opened = domain::detail::hpke_base_open_x25519(
            byte_string(32, 0x22),
            payload.substr(0, 32),
            {},
            sealed_blob_ad(DESTINATION_DOMAIN, Address{0x1234}, app_ctx),
            payload.substr(32));
        ASSERT_TRUE(opened.has_value());
        EXPECT_EQ(opened.value(), blob);
    }
}

TEST_F(ApplicationEncryptionContractTest, seal_rejects_truncated_arguments)
{
    state.set_nonce(SPOKE_CA, 1);
    state.set_storage(SPOKE_CA, DESTINATION_KEY_SLOT, RECIPIENT_KEY);
    auto const encoded =
        seal_input(byte_string(33, 0xab), byte_string(65, 0xcd));
    for (size_t size = 0; size < encoded.size(); ++size) {
        SCOPED_TRACE(size);
        auto const result = contract.precompile_seal(
            byte_string_view{encoded}.substr(0, size), Address{0x4321}, {});
        ASSERT_TRUE(result.has_error());
        EXPECT_EQ(result.assume_error(), AbiDecodeError::InputTooShort);
    }
}

TEST_F(ApplicationEncryptionContractTest, seal_rejects_trailing_bytes)
{
    state.set_nonce(SPOKE_CA, 1);
    state.set_storage(SPOKE_CA, DESTINATION_KEY_SLOT, RECIPIENT_KEY);

    for (auto const &suffix : {
             byte_string{0},
             byte_string{0xab},
             byte_string(32, 0),
             byte_string(33, 0xab),
         }) {
        SCOPED_TRACE(suffix.size());
        auto const result = contract.precompile_seal(
            seal_input() + suffix, Address{0x4321}, {});
        ASSERT_TRUE(result.has_error());
        EXPECT_EQ(result.assume_error(), AbiDecodeError::InputTooLong);
    }
}

TEST_F(ApplicationEncryptionContractTest, seal_rejects_nonzero_value)
{
    auto const result =
        contract.precompile_seal({}, Address{0x4321}, bytes32_t{1});
    ASSERT_TRUE(result.has_error());
    EXPECT_EQ(result.assume_error(), ApplicationEncryptionError::ValueNonZero);
}

TEST_F(ApplicationEncryptionContractTest, seal_changes_with_call_sequence)
{
    state.set_nonce(SPOKE_CA, 1);
    state.set_storage(SPOKE_CA, DESTINATION_KEY_SLOT, DESTINATION_KEY);
    auto const first = execute_seal();
    ASSERT_EQ(first.status_code, CallStatus::Success);
    EXPECT_EQ(host.call_sequence_, 1);
    auto const second = execute_seal();
    ASSERT_EQ(second.status_code, CallStatus::Success);
    EXPECT_EQ(host.call_sequence_, 2);
    EXPECT_NE(
        (byte_string_view{first.output_data, first.output_size}),
        (byte_string_view{second.output_data, second.output_size}));
}

TEST_F(
    ApplicationEncryptionContractTest, seal_message_changes_with_call_sequence)
{
    state.set_nonce(SPOKE_CA, 1);
    state.set_storage(SPOKE_CA, DESTINATION_KEY_SLOT, RECIPIENT_KEY);
    auto const plaintext = message_plaintext(byte_string{0xab});
    auto const first = execute_seal_message(plaintext);
    ASSERT_EQ(first.status_code, CallStatus::Success);
    auto const second = execute_seal_message(plaintext);
    ASSERT_EQ(second.status_code, CallStatus::Success);
    EXPECT_EQ(host.call_sequence_, 2);
    EXPECT_NE(
        (byte_string_view{first.output_data, first.output_size}),
        (byte_string_view{second.output_data, second.output_size}));
}

TEST_F(
    ApplicationEncryptionContractTest,
    seal_message_dispatches_solidity_selector)
{
    auto const arguments =
        seal_message_input(message_plaintext(byte_string{0xab}));

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
    ApplicationEncryptionContractTest, seal_message_round_trips_dynamic_bodies)
{
    state.set_nonce(SPOKE_CA, 1);
    state.set_storage(SPOKE_CA, DESTINATION_KEY_SLOT, RECIPIENT_KEY);
    auto const ad =
        sealed_message_ad(SOURCE_DOMAIN, DESTINATION_DOMAIN, MESSAGE_SEQUENCE);
    auto const wrong_ad = sealed_message_ad(
        SOURCE_DOMAIN, DESTINATION_DOMAIN, MESSAGE_SEQUENCE + 1);

    for (size_t const size : {0uz, 1uz, 31uz, 32uz, 33uz, 65uz}) {
        SCOPED_TRACE(size);
        auto const plaintext = message_plaintext(byte_string(size, 0xab));
        auto const result = contract.precompile_seal_message(
            seal_message_input(plaintext), SPOKE_CA, {});
        ASSERT_TRUE(result.has_value());

        byte_string_view output = result.value();
        auto const offset = abi_decode_fixed<u256_be>(output);
        ASSERT_TRUE(offset.has_value());
        EXPECT_EQ(offset.value().native(), 32);
        auto const decoded = abi_decode_dynamic_bytes_tail(output);
        ASSERT_TRUE(decoded.has_value());
        EXPECT_TRUE(output.empty());
        auto const payload = decoded.value();
        ASSERT_EQ(payload.size(), plaintext.size() + 32 + 16);

        byte_string const recipient_key(32, 0x22);
        auto const opened = domain::detail::hpke_base_open_x25519(
            recipient_key, payload.substr(0, 32), {}, ad, payload.substr(32));
        ASSERT_TRUE(opened.has_value());
        EXPECT_EQ(opened.value(), plaintext);
        EXPECT_TRUE(domain::detail::hpke_base_open_x25519(
                        recipient_key,
                        payload.substr(0, 32),
                        {},
                        wrong_ad,
                        payload.substr(32))
                        .has_error());
    }
}

TEST_F(
    ApplicationEncryptionContractTest,
    dispatch_seal_message_matches_independent_ciphertext_vector)
{
    state.set_nonce(SPOKE_CA, 1);
    state.set_storage(SPOKE_CA, DESTINATION_KEY_SLOT, RECIPIENT_KEY);
    auto const plaintext = message_plaintext(byte_string{0xab});
    auto const result = execute_seal_message(plaintext);
    ASSERT_EQ(result.status_code, CallStatus::Success);

    // Generated in Python by encoding the ABI words, deriving the ephemeral
    // input with HMAC-SHA256, and applying RFC 9180 labeled HKDF.
    // Python cryptography 50.0.2 supplies X25519 and AES-GCM.
    // Call sequence is 1. Source and recipient private keys are 0x11 * 32 and
    // 0x22 * 32.
    auto const expected =
        from_hex(
            "0000000000000000000000000000000000000000000000000000000000000020"
            "00000000000000000000000000000000000000000000000000000000000000d0"
            "a51b2cfd4632d81d220c158d80ba542d5361aa809fd2886ab777f3ec42e6d346"
            "f30a8910f6e3b9598bfa65abee04a2c76701befd9aa5537a18673bef3a9f59cd"
            "885c4425e2649c75c75949cd073f25653648057005ca343b17fe9220101f0ddb"
            "6b9b44ca0a37f2d7f0969f024029d1e9203c17d91d9e633d410e3482c6a460d8"
            "fa77de8591449623fe61dd4137f3efa3e579508cba55b0a60790219cf12fffd9"
            "37c0c90060f9bcb1164f222985d5e5adc55aaaf9a89127415ad1dd9c667c10bd"
            "47f104c7dd12362ff278db60e52855af00000000000000000000000000000000")
            .value();
    EXPECT_EQ(
        (byte_string_view{result.output_data, result.output_size}), expected);
}

TEST_F(
    ApplicationEncryptionContractTest, seal_message_rejects_truncated_arguments)
{
    auto const encoded =
        seal_message_input(message_plaintext(byte_string(33, 0xab)));

    for (size_t size = 0; size < encoded.size(); ++size) {
        SCOPED_TRACE(size);
        auto const input = byte_string_view{encoded}.substr(0, size);
        auto const result =
            contract.precompile_seal_message(input, SPOKE_CA, {});
        ASSERT_TRUE(result.has_error());
        EXPECT_EQ(result.assume_error(), AbiDecodeError::InputTooShort);
    }
}

TEST_F(ApplicationEncryptionContractTest, seal_message_rejects_invalid_calldata)
{
    auto const truncated_from =
        contract.precompile_seal_message(seal_message_input({}), SPOKE_CA, {});
    ASSERT_TRUE(truncated_from.has_error());
    EXPECT_EQ(truncated_from.assume_error(), AbiDecodeError::InputTooShort);

    auto input = seal_message_input(message_plaintext(byte_string{0xab}));
    input.push_back(0);
    auto const trailing = contract.precompile_seal_message(input, SPOKE_CA, {});
    ASSERT_TRUE(trailing.has_error());
    EXPECT_EQ(trailing.assume_error(), AbiDecodeError::InputTooLong);

    input.pop_back();
    input[3 * sizeof(u256_be) - 1] = 0;
    auto const bad_offset =
        contract.precompile_seal_message(input, SPOKE_CA, {});
    ASSERT_TRUE(bad_offset.has_error());
    EXPECT_EQ(bad_offset.assume_error(), AbiDecodeError::InvalidEncoding);
}

TEST_F(
    ApplicationEncryptionContractTest, dispatch_seal_message_rejects_non_spoke)
{
    state.set_nonce(SPOKE_CA, 1);
    state.set_storage(SPOKE_CA, DESTINATION_KEY_SLOT, RECIPIENT_KEY);
    auto const result = execute_seal_message(
        message_plaintext(byte_string{0xab}), MESSAGE_FROM);
    ASSERT_EQ(result.status_code, CallStatus::Revert);
    EXPECT_EQ(
        (std::string_view{
            reinterpret_cast<char const *>(result.output_data),
            result.output_size}),
        "application encryption caller is not authorized");
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
    auto const input = seal_message_input(message_plaintext(byte_string{0xab}));

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

    state.set_storage(SPOKE_CA, DESTINATION_KEY_SLOT, RECIPIENT_KEY);
    auto const installed =
        contract.precompile_seal_message(input, SPOKE_CA, {});
    EXPECT_TRUE(installed.has_value());
}

TEST_F(ApplicationEncryptionContractTest, seal_message_rejects_invalid_key)
{
    state.set_nonce(SPOKE_CA, 1);
    bytes32_t low_order_key{};
    low_order_key.bytes[0] = 1;
    state.set_storage(SPOKE_CA, DESTINATION_KEY_SLOT, low_order_key);
    auto const result = contract.precompile_seal_message(
        seal_message_input(message_plaintext(byte_string{0xab})), SPOKE_CA, {});
    ASSERT_TRUE(result.has_error());
    EXPECT_EQ(result.assume_error(), ApplicationEncryptionError::SealFailed);
}

TEST(ApplicationEncryptionMessageEncoding, matches_abi_fixtures)
{
    // Generated with Python using 32-byte big-endian words, offsets relative
    // to the tuple start, and length-prefixed, zero-padded dynamic tails.
    auto const expected_ad =
        from_hex(
            "0000000000000000000000000000000000000000000000000000000000000080"
            "0000000000000000000000000000000000000000000000000000520000004eaf"
            "0000000000000000000000000000000000000000000000000000510000004eaf"
            "0000000000000100000000000000000000000000000000000000000000000007"
            "0000000000000000000000000000000000000000000000000000000000000020"
            "6d6f6e61642d63726f73732d646f6d61696e2d656e6372797074696f6e2d7631")
            .value();
    EXPECT_EQ(
        sealed_message_ad(SOURCE_DOMAIN, DESTINATION_DOMAIN, MESSAGE_SEQUENCE),
        expected_ad);

    // The original sender and transaction origin occupy distinct head words.
    auto const expected_randomness_input =
        from_hex(
            "0000000000000000000000000000000000000000000000000000000000000120"
            "0000000000000100000000000000000000000000000000000000000000000007"
            "0000000000000000000000000000000000000000000000000000000000004321"
            "00000000000000000000000089abcdef0123456789abcdef0123456789abcdef"
            "000000000000000000000000000000000000000000000000fedcba9876543210"
            "0000000000000000000000000000000000000000000000000000000100000007"
            "0000000000000000000000000000000000000000000000000000000000000160"
            "00000000000000000000000000000000000000000000000000000000000001a0"
            "00000000000000000000000000000000000000000000000000000000000001e0"
            "0000000000000000000000000000000000000000000000000000000000000020"
            "6d6f6e61642d63726f73732d646f6d61696e2d72616e646f6d6e6573732d7631"
            "0000000000000000000000000000000000000000000000000000000000000020"
            "000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f"
            "0000000000000000000000000000000000000000000000000000000000000002"
            "0102000000000000000000000000000000000000000000000000000000000000"
            "0000000000000000000000000000000000000000000000000000000000000002"
            "0003000000000000000000000000000000000000000000000000000000000000")
            .value();
    EXPECT_EQ(
        sealed_message_randomness_input(
            MESSAGE_SEQUENCE,
            MESSAGE_FROM,
            TX_ORIGIN,
            TX_NONCE,
            0x100000007,
            DESTINATION_KEY,
            byte_string{0x01, 0x02},
            byte_string{0x00, 0x03}),
        expected_randomness_input);
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
    // length-prefixed tails. The nonce and call sequence exceed uint32_t; the
    // blob spans two words and the public key contains a leading zero byte.
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

struct ApplicationEncryptionCallSequenceTest
    : ApplicationEncryptionContractTest
    , ::testing::WithParamInterface<vm::VM::Mode>
{
    static constexpr Address CALLER{0x5678};

    ApplicationEncryptionCallSequenceTest()
        : ApplicationEncryptionContractTest{GetParam()}
    {
        state.set_nonce(SPOKE_CA, 1);
        state.set_storage(SPOKE_CA, DESTINATION_KEY_SLOT, DESTINATION_KEY);
    }

    vm::Result execute_wrapper(uint8_t const exit_opcode)
    {
        // Copy calldata, CALL ALE, copy its return data, then RETURN, REVERT
        // or halt exceptionally. The wrapper and its child share one host.
        auto code =
            from_hex("365f5f375f5f365f5f611a7e5af1503d5f5f3e3d5f").value();
        code.push_back(exit_opcode);
        state.set_nonce(CALLER, 1);
        state.set_code(CALLER, code);
        auto const input = seal_calldata();
        auto message = seal_call(input);
        message.recipient = CALLER;
        message.code_address = CALLER;
        message.gas = 100'000;
        return execute_message(message);
    }
};

TEST_P(ApplicationEncryptionCallSequenceTest, revert_retains_descendant_calls)
{
    auto const reverted = execute_wrapper(vm::compiler::EvmOpCode::REVERT);
    ASSERT_EQ(reverted.status_code, CallStatus::Revert);
    ASSERT_GT(reverted.output_size, 0);
    EXPECT_EQ(host.call_sequence_, 2);

    // Call the wrapper again with identical input. Its ALE call must use
    // sequence 4; resetting on REVERT would reuse sequence 2 and its
    // ciphertext.
    auto const next = execute_wrapper(vm::compiler::EvmOpCode::REVERT);
    ASSERT_EQ(next.status_code, CallStatus::Revert);
    ASSERT_GT(next.output_size, 0);
    EXPECT_EQ(host.call_sequence_, 4);
    EXPECT_NE(
        (byte_string_view{reverted.output_data, reverted.output_size}),
        (byte_string_view{next.output_data, next.output_size}));
}

TEST_P(
    ApplicationEncryptionCallSequenceTest,
    exceptional_halt_restores_pre_call_sequence)
{
    host.call_sequence_ = 7;
    // Pass INVALID as the final opcode
    auto const failed = execute_wrapper(0xfe);
    EXPECT_EQ(failed.status_code, CallStatus::Failure);
    EXPECT_EQ(failed.output_size, 0);
    EXPECT_EQ(host.call_sequence_, 7);

    auto const result = execute_seal();
    ASSERT_EQ(result.status_code, CallStatus::Success);
    EXPECT_EQ(host.call_sequence_, 8);
}

TEST_P(
    ApplicationEncryptionCallSequenceTest,
    stack_underflow_reconciles_engine_call_sequences)
{
    // CALL leaves one success flag. The second POP underflows in the same
    // block: the compiler rejects it before CALL, while the interpreter
    // reaches ALE before failing.
    // Each test owns a fresh VM, so Dual interprets this first execution.
    auto const code = from_hex("365f5f375f5f365f5f611a7e5af15050").value();
    state.set_nonce(CALLER, 1);
    state.set_code(CALLER, code);

    std::vector<CallFrame> frames;
    CallTracer tracer{tx, frames};
    StateHost<traits> traced_host{
        tracer,
        state_tracer,
        tx_context,
        block_hashes,
        state,
        tx,
        std::nullopt,
        0,
        chain_ctx};
    traced_host.call_sequence_ = 7;
    auto const input = seal_calldata();
    auto message = seal_call(input);
    message.recipient = CALLER;
    message.code_address = CALLER;
    message.gas = 100'000;
    auto const failed = execute_message(message, traced_host);
    EXPECT_EQ(failed.status_code, CallStatus::Failure);
    EXPECT_EQ(failed.output_size, 0);
    EXPECT_EQ(failed.gas_left, 0);

    auto const compiled = GetParam() == vm::VM::CompilerOnly;
    ASSERT_EQ(frames.size(), compiled ? 1 : 2);
    EXPECT_EQ(frames[0].to, CALLER);
    if (!compiled) {
        EXPECT_EQ(frames[1].to, ALE_CA);
        EXPECT_EQ(frames[1].status, CallStatus::Success);
        EXPECT_FALSE(frames[1].output.empty());
    }
    EXPECT_EQ(traced_host.call_sequence_, 7);

    auto const next = execute_message(seal_call(input), traced_host);
    ASSERT_EQ(next.status_code, CallStatus::Success);
    EXPECT_EQ(traced_host.call_sequence_, 8);

    // Compare this mode's next Seal with the same direct sequence-8 reference.
    // Calls inside the discarded frame must not affect the ciphertext.
    ApplicationEncryptionContract direct{
        state, call_tracer, encryption_context, TX_ORIGIN, TX_NONCE, 8};
    auto const expected =
        direct.precompile_seal(seal_input(), Address{0x4321}, {});
    ASSERT_TRUE(expected.has_value());
    EXPECT_EQ(
        (byte_string_view{next.output_data, next.output_size}),
        expected.value());
}

TEST_P(ApplicationEncryptionCallSequenceTest, create_initcode_shares_counter)
{
    // CALL the identity precompile, then deploy empty runtime code.
    auto const initcode = from_hex("5f5f5f5f5f60045af1505f5ff3").value();
    for (auto const kind : {vm::CallKind::Create, vm::CallKind::Create2}) {
        SCOPED_TRACE(static_cast<int>(kind));
        auto message = seal_call(initcode);
        message.kind = kind;
        message.gas = 100'000;
        auto const previous = host.call_sequence_;
        auto const result = execute_message(message);
        ASSERT_EQ(result.status_code, CallStatus::Success);
        EXPECT_EQ(result.output_size, 0);
        EXPECT_EQ(host.call_sequence_, previous + 2);
    }
}

TEST_P(
    ApplicationEncryptionCallSequenceTest,
    code_deposit_failure_restores_pre_call_sequence)
{
    // CALL identity, then return 1024 bytes: code deposit exceeds 100,000 gas.
    auto const initcode = from_hex("5f5f5f5f5f60045af1506104005ff3").value();
    for (auto const kind : {vm::CallKind::Create, vm::CallKind::Create2}) {
        SCOPED_TRACE(static_cast<int>(kind));
        auto message = seal_call(initcode);
        message.kind = kind;
        message.gas = 100'000;
        auto const previous = host.call_sequence_;
        auto const result = execute_message(message);
        EXPECT_EQ(result.status_code, CallStatus::OutOfGas);
        EXPECT_EQ(result.output_size, 0);
        EXPECT_EQ(host.call_sequence_, previous);
    }
}

INSTANTIATE_TEST_SUITE_P(
    VmBackends, ApplicationEncryptionCallSequenceTest,
    ::testing::Values(
        vm::VM::InterpreterOnly, vm::VM::CompilerOnly, vm::VM::Dual));

TEST_F(ApplicationEncryptionContractTest, call_sequence_is_local_to_host)
{
    State other_state{block_state, Incarnation{0, 1}};
    StateHost<traits> other{
        call_tracer,
        state_tracer,
        tx_context,
        block_hashes,
        other_state,
        tx,
        std::nullopt,
        1,
        chain_ctx};
    EXPECT_EQ(host.call_sequence_, 0);
    EXPECT_EQ(other.call_sequence_, 0);
    vm::Message const message{
        .kind = vm::CallKind::Call,
        .depth = 1,
        .gas = 1'000,
        .recipient = Address{4},
        .code_address = Address{4}};
    ASSERT_EQ(host.call(message).status_code, CallStatus::Success);
    ASSERT_EQ(other.call(message).status_code, CallStatus::Success);
    ASSERT_EQ(host.call(message).status_code, CallStatus::Success);
    EXPECT_EQ(host.call_sequence_, 2);
    EXPECT_EQ(other.call_sequence_, 1);
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
