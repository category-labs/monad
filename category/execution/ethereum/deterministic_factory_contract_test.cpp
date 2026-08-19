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
#include <category/core/byte_string.hpp>
#include <category/core/bytes.hpp>
#include <category/core/hex.hpp>
#include <category/core/int.hpp>
#include <category/core/keccak.hpp>
#include <category/execution/ethereum/block_hash_buffer.hpp>
#include <category/execution/ethereum/core/block.hpp>
#include <category/execution/ethereum/core/transaction.hpp>
#include <category/execution/ethereum/create_contract_address.hpp>
#include <category/execution/ethereum/db/trie_db.hpp>
#include <category/execution/ethereum/deterministic_factory_contract.hpp>
#include <category/execution/ethereum/evmc_host.hpp>
#include <category/execution/ethereum/state2/block_state.hpp>
#include <category/execution/ethereum/state3/state.hpp>
#include <category/execution/ethereum/trace/call_tracer.hpp>
#include <category/execution/ethereum/trace/state_tracer.hpp>
#include <category/execution/ethereum/tx_context.hpp>
#include <category/execution/ethereum/types/incarnation.hpp>
#include <category/execution/monad/chain/monad_devnet.hpp>
#include <category/mpt/db.hpp>
#include <category/vm/code.hpp>
#include <category/vm/evm/traits.hpp>
#include <category/vm/utils/evm-as.hpp>
#include <category/vm/vm.hpp>
#include <monad/test/traits_test.hpp>

#include <evmc/evmc.h>
#include <evmc/evmc.hpp>
#include <gtest/gtest.h>

#include <cstdint>
#include <memory>
#include <vector>

using namespace monad;

namespace
{
    // Independent copy of the EIP-7997 runtime bytecode (Arachnid's
    // deterministic deployment proxy), so a typo in the deployed constant
    // is caught rather than compared against itself.
    byte_string const EXPECTED_FACTORY_CODE =
        from_hex(
            "0x7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff"
            "fe03601600081602082378035828234f58015156039578182fd5b808252505050"
            "6014600cf3")
            .value();

    template <typename T>
    struct DeterministicFactoryTest : public ::testing::Test
    {
        static constexpr auto get_trait()
        {
            if constexpr (std::
                              same_as<typename T::value_type, monad_revision>) {
                return monad::MonadTraits<T::value>{};
            }
            else {
                return monad::EvmTraits<T::value>{};
            }
        }

        using Trait = decltype(get_trait());

        mpt::Db db;
        TrieDb tdb;
        vm::VM vm;
        BlockState block_state;
        State state;

        DeterministicFactoryTest()
            : db{std::make_unique<InMemoryMachine>()}
            , tdb{db}
            , block_state{tdb, vm}
            , state{block_state, Incarnation{0, 0}}
        {
        }

        void deploy()
        {
            deploy_deterministic_factory_contract<Trait>(state);
        }

        byte_string_view code_at(Address const &addr)
        {
            auto const icode = state.get_code(addr)->intercode();
            return {icode->code(), icode->size()};
        }

        void expect_factory_deployed()
        {
            EXPECT_TRUE(
                state.account_has_code_or_nonce(DETERMINISTIC_FACTORY_ADDRESS));
            EXPECT_EQ(state.get_nonce(DETERMINISTIC_FACTORY_ADDRESS), 1);
            EXPECT_EQ(
                code_at(DETERMINISTIC_FACTORY_ADDRESS), EXPECTED_FACTORY_CODE);
        }

        // Initcode that deploys the single-byte runtime `0xAA`.
        static std::vector<uint8_t> trivial_initcode()
        {
            using namespace monad::vm::utils;

            auto eb = evm_as::EvmBuilder<Trait>{};
            eb.push(0xAA).push0().mstore8().push(1).push0().return_();
            std::vector<uint8_t> bytecode{};
            EXPECT_TRUE(evm_as::validate(eb));
            evm_as::compile(eb, bytecode);
            return bytecode;
        }

        // Call the factory with `salt || initcode` as calldata, as a user
        // would, and return the raw execution result.
        evmc::Result call_factory(
            bytes32_t const &salt, std::vector<uint8_t> const &initcode)
        {
            static constexpr Address sender =
                0xcccccccccccccccccccccccccccccccccccccccc_address;

            byte_string calldata{salt.bytes, sizeof(salt.bytes)};
            calldata.append(initcode.data(), initcode.size());

            MonadDevnet const chain{};
            Transaction const tx{};
            BlockHeader const header{.number = 1};
            evmc_tx_context const tx_context = get_tx_context<Trait>(
                tx,
                sender,
                header,
                chain.get_chain_id(),
                chain.get_blob_schedule(header.timestamp));
            NoopCallTracer call_tracer{};
            trace::StateTracer noop_state_tracer = std::monostate{};
            BlockHashBufferFinalized const buffer{};
            uint256_t base_fee{0};
            EvmcHost<Trait> host{
                call_tracer,
                noop_state_tracer,
                tx_context,
                buffer,
                state,
                tx,
                base_fee,
                0,
                ChainContext<Trait>::debug_empty()};

            auto msg_memory = state.vm().message_memory_ref();
            evmc_message const msg{
                .kind = EVMC_CALL,
                .gas = 1'000'000,
                .recipient = DETERMINISTIC_FACTORY_ADDRESS,
                .sender = sender,
                .input_data = calldata.data(),
                .input_size = calldata.size(),
                .code_address = DETERMINISTIC_FACTORY_ADDRESS,
                .memory_handle = msg_memory.get(),
                .memory = msg_memory.get(),
                .memory_capacity = state.vm().message_memory_capacity()};
            auto const hash = state.get_code_hash(msg.code_address);
            auto const &code = state.read_code(hash);
            return state.vm().template execute<Trait>(host, &msg, hash, code);
        }
    };
}

TYPED_TEST_SUITE(
    DeterministicFactoryTest, ::detail::MonadEvmRevisionTypes,
    ::detail::RevisionTestNameGenerator);

TYPED_TEST(DeterministicFactoryTest, deploys_when_active)
{
    TestFixture::deploy();

    if constexpr (TestFixture::Trait::eip_7997_active()) {
        TestFixture::expect_factory_deployed();
        EXPECT_EQ(this->state.get_balance(DETERMINISTIC_FACTORY_ADDRESS), 0);
    }
    else {
        EXPECT_FALSE(this->state.account_exists(DETERMINISTIC_FACTORY_ADDRESS));
    }
}

TYPED_TEST(DeterministicFactoryTest, idempotent)
{
    TestFixture::deploy();
    TestFixture::deploy();

    if constexpr (TestFixture::Trait::eip_7997_active()) {
        TestFixture::expect_factory_deployed();
    }
    else {
        EXPECT_FALSE(this->state.account_exists(DETERMINISTIC_FACTORY_ADDRESS));
    }
}

TYPED_TEST(DeterministicFactoryTest, deploys_over_balance_only_account)
{
    // A value transfer to the factory address before activation must not
    // prevent deployment, and the balance must survive it.
    uint256_t const balance{1234};
    this->state.add_to_balance(DETERMINISTIC_FACTORY_ADDRESS, balance);
    ASSERT_TRUE(this->state.account_exists(DETERMINISTIC_FACTORY_ADDRESS));
    ASSERT_FALSE(
        this->state.account_has_code_or_nonce(DETERMINISTIC_FACTORY_ADDRESS));

    TestFixture::deploy();

    EXPECT_EQ(this->state.get_balance(DETERMINISTIC_FACTORY_ADDRESS), balance);
    if constexpr (TestFixture::Trait::eip_7997_active()) {
        TestFixture::expect_factory_deployed();
    }
    else {
        EXPECT_FALSE(this->state.account_has_code_or_nonce(
            DETERMINISTIC_FACTORY_ADDRESS));
    }
}

TYPED_TEST(DeterministicFactoryTest, does_not_clobber_existing_contract)
{
    // If the address already holds code or a nonce, deployment is skipped
    // regardless of activation.
    byte_string const other_code = from_hex("0x00").value();
    this->state.create_contract(DETERMINISTIC_FACTORY_ADDRESS);
    this->state.set_code(DETERMINISTIC_FACTORY_ADDRESS, other_code);
    this->state.set_nonce(DETERMINISTIC_FACTORY_ADDRESS, 5);

    TestFixture::deploy();

    EXPECT_EQ(this->state.get_nonce(DETERMINISTIC_FACTORY_ADDRESS), 5);
    EXPECT_EQ(TestFixture::code_at(DETERMINISTIC_FACTORY_ADDRESS), other_code);
}

TYPED_TEST(DeterministicFactoryTest, create2_deploys_at_expected_address)
{
    if constexpr (!TestFixture::Trait::eip_7997_active()) {
        GTEST_SKIP() << "EIP-7997 not active for this revision";
    }
    else {
        TestFixture::deploy();

        bytes32_t const salt = to_bytes(uint256_t{0x1234});
        auto const initcode = TestFixture::trivial_initcode();
        byte_string_view const initcode_view{initcode.data(), initcode.size()};
        Address const expected = create2_contract_address(
            DETERMINISTIC_FACTORY_ADDRESS, salt, keccak256(initcode_view));

        auto const result = TestFixture::call_factory(salt, initcode);
        ASSERT_EQ(result.status_code, EVMC_SUCCESS);
        ASSERT_EQ(result.output_size, sizeof(Address));
        Address actual{};
        memcpy(actual.bytes, result.output_data, sizeof(Address));
        EXPECT_EQ(actual, expected);

        // The deployed contract has the runtime code emitted by the initcode,
        // and CREATE2 bumped the factory's nonce.
        EXPECT_EQ(TestFixture::code_at(expected), from_hex("0xaa").value());
        EXPECT_EQ(this->state.get_nonce(expected), 1);
        EXPECT_EQ(this->state.get_nonce(DETERMINISTIC_FACTORY_ADDRESS), 2);
    }
}

TYPED_TEST(DeterministicFactoryTest, create2_collision_reverts)
{
    if constexpr (!TestFixture::Trait::eip_7997_active()) {
        GTEST_SKIP() << "EIP-7997 not active for this revision";
    }
    else {
        TestFixture::deploy();

        bytes32_t const salt = to_bytes(uint256_t{0x5678});
        auto const initcode = TestFixture::trivial_initcode();

        auto const first = TestFixture::call_factory(salt, initcode);
        ASSERT_EQ(first.status_code, EVMC_SUCCESS);

        // Same salt and initcode: CREATE2 fails on the address collision and
        // the proxy reverts with no data.
        auto const second = TestFixture::call_factory(salt, initcode);
        EXPECT_EQ(second.status_code, EVMC_REVERT);
        EXPECT_EQ(second.output_size, 0);
    }
}
