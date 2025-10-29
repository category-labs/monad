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

#include <category/core/bytes.hpp>
#include <category/core/int.hpp>
#include <category/execution/ethereum/block_hash_buffer.hpp>
#include <category/execution/ethereum/block_hash_history.hpp>
#include <category/execution/ethereum/core/transaction.hpp>
#include <category/execution/ethereum/db/trie_db.hpp>
#include <category/execution/ethereum/evmc_host.hpp>
#include <category/execution/ethereum/state2/block_state.hpp>
#include <category/execution/ethereum/state3/state.hpp>
#include <category/execution/ethereum/tx_context.hpp>
#include <category/execution/monad/chain/monad_devnet.hpp>
#include <category/mpt/db.hpp>
#include <category/vm/evm/traits.hpp>
#include <category/vm/utils/evm-as.hpp>
#include <monad/test/traits_test.hpp>
#include <test_resource_data.h>

#include <gtest/gtest.h>

#include <cstdint>

using namespace monad;
using namespace monad::test;

namespace
{
    // Byte encode 64 bit integers in 256 bit big endian format.
    bytes32_t enc(uint64_t const x)
    {
        return to_bytes(to_big_endian(uint256_t{x}));
    }

    struct BlockHashHistoryTest : public ::testing::Test
    {
        InMemoryMachine machine;
        mpt::Db db;
        TrieDb tdb;
        vm::VM vm;
        BlockState block_state;
        State state;
        BlockHashBufferFinalized block_hash_buffer;
        static constexpr Address blockhash_opcode_addr =
            0x00000000000000000000000000000000000123_address;

        BlockHashHistoryTest()
            : db{machine}
            , tdb{db}
            , block_state{tdb, vm}
            , state{block_state, Incarnation{0, 0}}
            , block_hash_buffer{}
        {
        }

        void deploy_history_contract();
        void fill_history(uint64_t const, uint64_t const);
        void
        fill_history_fixed(uint64_t const, uint64_t const, bytes32_t const &);
    };

    void BlockHashHistoryTest::deploy_history_contract()
    {
        BlockHeader const header{.parent_hash = bytes32_t{}, .number = 0};
        deploy_block_hash_history_contract(state);
    }

    void BlockHashHistoryTest::fill_history(
        uint64_t const start_block, uint64_t const end_block)
    {
        // We populate the history contract with simple "hashes" for ease of
        // testing. Key: block number - 1 in big endian. Value: block number - 1
        // in little endian. Note, special mapping: 0 -> 0.
        for (uint64_t i = start_block; i <= end_block; i++) {
            BlockHeader const header{
                .parent_hash = to_bytes(i - 1), .number = i};
            set_block_hash_history(
                state, header); // sets `number - 1 -> to_bytes(number - 1)`
        }
    }

    void BlockHashHistoryTest::fill_history_fixed(
        uint64_t const start_block, uint64_t const end_block,
        bytes32_t const &fixed_hash)
    {
        for (uint64_t i = start_block; i <= end_block; i++) {
            BlockHeader const header{.parent_hash = fixed_hash, .number = i};
            set_block_hash_history(
                state, header); // sets `number - 1 -> fixed_hash`
        }
    }

    template <typename T>
    struct BlockHashHistoryTraitsTest : public BlockHashHistoryTest
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

        evmc::Result call(
            uint64_t const current_block_number, Address sender,
            Address code_addr, std::uint8_t const *input_data,
            std::uint32_t input_size, int64_t gas,
            BlockHashBufferFinalized const &buffer)
        {
            MonadDevnet const chain{};

            Transaction const tx{};
            BlockHeader const header = {.number = current_block_number};
            evmc_tx_context const tx_context =
                get_tx_context<Trait>(tx, sender, header, chain.get_chain_id());
            NoopCallTracer call_tracer{};
            EvmcHost<Trait> host{call_tracer, tx_context, buffer, state};

            evmc_message const msg{
                .kind = EVMC_CALL,
                .gas = gas,
                .recipient = code_addr,
                .sender = sender,
                .input_data = input_data,
                .input_size = input_size,
                .code_address = code_addr};
            auto const hash = state.get_code_hash(msg.code_address);
            auto const &code = state.read_code(hash);
            return state.vm().template execute<Trait>(host, &msg, hash, code);
        }

        evmc::Result call_blockhash_opcode(
            uint64_t const block_number, uint64_t const current_block_number,
            Address sender = 0xcccccccccccccccccccccccccccccccccccccccc_address)
        {
            auto const calldata = enc(block_number);
            auto const input_size = 32;
            return call(
                current_block_number,
                sender,
                blockhash_opcode_addr,
                calldata.bytes,
                input_size,
                100'000,
                block_hash_buffer);
        }

        void deploy_contract_that_uses_blockhash()
        {
            // Deploy test contract
            using namespace monad::vm::utils;

            // execute `blockhash <block number from calldata>`
            auto eb = evm_as::EvmBuilder<Trait>{};
            eb.push0()
                .calldataload()
                .blockhash()
                .push0()
                .mstore()
                .push(0x20)
                .push0()
                .return_();
            std::vector<uint8_t> bytecode{};
            ASSERT_TRUE(evm_as::validate(eb));
            evm_as::compile(eb, bytecode);

            byte_string_view const bytecode_view{
                bytecode.data(), bytecode.size()};
            bytes32_t const code_hash = to_bytes(keccak256(bytecode_view));

            // Deploy test contract
            state.create_contract(blockhash_opcode_addr);
            state.set_code_hash(blockhash_opcode_addr, code_hash);
            state.set_code(blockhash_opcode_addr, bytecode_view);
            state.set_nonce(blockhash_opcode_addr, 1);
        }
    };

}

TYPED_TEST_SUITE(
    BlockHashHistoryTraitsTest,
    ::detail::MonadEvmRevisionTypesSince<EVMC_PRAGUE>,
    ::detail::RevisionTestNameGenerator);
