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
#include <category/core/keccak.hpp>
#include <category/execution/ethereum/chain/ethereum_mainnet.hpp>
#include <category/execution/ethereum/chain/genesis_state.hpp>
#include <category/execution/ethereum/core/block.hpp>
#include <category/execution/ethereum/core/rlp/block_rlp.hpp>
#include <category/execution/ethereum/core/transaction.hpp>
#include <category/execution/ethereum/db/trie_db.hpp>
#include <category/execution/ethereum/state2/block_state.hpp>
#include <category/execution/ethereum/state3/state.hpp>
#include <category/execution/ethereum/transaction_gas.hpp>
#include <category/execution/ethereum/validate_block.hpp>
#include <category/execution/ethereum/validate_transaction.hpp>
#include <category/execution/monad/chain/monad_chain.hpp>
#include <category/execution/monad/chain/monad_devnet.hpp>
#include <category/execution/monad/chain/monad_mainnet.hpp>
#include <category/execution/monad/chain/monad_testnet.hpp>
#include <category/execution/monad/chain/monad_testnet2.hpp>
#include <category/execution/monad/reserve_balance.h>
#include <category/execution/monad/reserve_balance.hpp>
#include <category/execution/monad/system_sender.hpp>
#include <category/execution/monad/validate_monad_transaction.hpp>
#include <category/mpt/db.hpp>
#include <category/vm/evm/switch_traits.hpp>
#include <monad/test/traits_test.hpp>

#include <bitset>

#include <gtest/gtest.h>

using namespace monad;

TYPED_TEST(MonadTraitsTest, compute_gas_refund)
{
    uint64_t const refund = compute_gas_refund<typename TestFixture::Trait>(
        Transaction{.gas_limit = 21'000}, 20'000, 1'000);
    if constexpr (TestFixture::REV >= MONAD_FIVE) {
        EXPECT_EQ(refund, 1'000);
    }
    else if constexpr (TestFixture::REV >= MONAD_ONE) {
        EXPECT_EQ(refund, 0);
    }
    else {
        EXPECT_EQ(refund, 20'200);
    }
}

TEST(MonadChain, Genesis)
{
    {
        InMemoryMachine machine;
        mpt::Db db{machine};
        TrieDb tdb{db};
        MonadTestnet const chain;
        load_genesis_state(chain.get_genesis_state(), tdb);
        BlockHeader const header = tdb.read_eth_header();
        bytes32_t const hash =
            to_bytes(keccak256(rlp::encode_block_header(header)));
        EXPECT_EQ(
            hash,
            0x1436534e54a22183ea29a2273b341cb50018ed066441ffd111cd263297caba35_bytes32);
        EXPECT_TRUE(static_validate_header<EvmTraits<EVMC_FRONTIER>>(header)
                        .has_value());
        // the header generated at the time was not a valid header for the
        // cancun revision
        EXPECT_FALSE(
            static_validate_header<EvmTraits<EVMC_CANCUN>>(header).has_value());
    }

    {
        InMemoryMachine machine;
        mpt::Db db{machine};
        TrieDb tdb{db};
        MonadDevnet const chain;
        load_genesis_state(chain.get_genesis_state(), tdb);
        BlockHeader const header = tdb.read_eth_header();
        bytes32_t const hash =
            to_bytes(keccak256(rlp::encode_block_header(header)));
        EXPECT_EQ(
            hash,
            0xb711505d8f46fc921ae824f847f26c5c3657bf6c8b9dcf07ffdf3357a143bca9_bytes32);
        EXPECT_TRUE(static_validate_header<EvmTraits<EVMC_FRONTIER>>(header)
                        .has_value());
        // the header generated at the time was not a valid header for the
        // cancun revision
        EXPECT_FALSE(
            static_validate_header<EvmTraits<EVMC_CANCUN>>(header).has_value());
    }
    {
        InMemoryMachine machine;
        mpt::Db db{machine};
        TrieDb tdb{db};
        MonadMainnet const chain;
        load_genesis_state(chain.get_genesis_state(), tdb);
        BlockHeader const header = tdb.read_eth_header();
        bytes32_t const hash =
            to_bytes(keccak256(rlp::encode_block_header(header)));
        EXPECT_EQ(
            hash,
            0x0c47353304f22b1c15706367d739b850cda80b5c87bbc335014fef3d88deaac9_bytes32);
        EXPECT_TRUE(
            static_validate_header<EvmTraits<EVMC_CANCUN>>(header).has_value());
    }
    {
        InMemoryMachine machine;
        mpt::Db db{machine};
        TrieDb tdb{db};
        MonadTestnet2 const chain;
        load_genesis_state(chain.get_genesis_state(), tdb);
        BlockHeader const header = tdb.read_eth_header();
        bytes32_t const hash =
            to_bytes(keccak256(rlp::encode_block_header(header)));
        EXPECT_EQ(
            hash,
            0x2a2544bf6d096df891903c8fa14e9914009e6bc9d448399585961a3044e03e50_bytes32);
        EXPECT_TRUE(
            static_validate_header<EvmTraits<EVMC_CANCUN>>(header).has_value());
    }
}

enum PreventDipBits
{
    IsDelegated = 0,
    SenderOrAuthorityInGrandparent = 1,
    SenderOrAuthorityInParent = 2,
    SenderInBlock = 3,
    AuthorityInBlock = 4,
    AuthorityInTransaction = 5,
};

constexpr uint8_t PREVENT_DIP_BITS_POWERSET_SIZE = 64;

static_assert(
    (1 << (AuthorityInTransaction + 1)) == PREVENT_DIP_BITS_POWERSET_SIZE);

void run_revert_transaction_test(
    uint8_t const prevent_dip_bitset, uint64_t const initial_balance_mon,
    uint64_t const gas_fee_mon, uint64_t const value_mon, bool const expected)
{
    constexpr uint256_t BASE_FEE_PER_GAS = 10;
    constexpr Address SENDER{1};
    MonadDevnet const chain;
    InMemoryMachine machine;
    mpt::Db db{machine};
    TrieDb tdb{db};
    vm::VM vm;
    BlockState bs{tdb, vm};

    ASSERT_EQ(
        monad_default_max_reserve_balance_mon(chain.get_monad_revision(0)), 10);

    // Set up initial state
    {
        State state{bs, Incarnation{0, 0}};
        uint256_t const initial_balance =
            uint256_t{initial_balance_mon} * 1000000000000000000ULL;
        state.add_to_balance(SENDER, initial_balance);
        if (prevent_dip_bitset & (1 << IsDelegated)) {
            byte_string const code{
                0xef, 0x01, 0x00, 0x02, 0x02, 0x02, 0x02, 0x02,
                0x02, 0x02, 0x02, 0x02, 0x02, 0x02, 0x02, 0x02,
                0x02, 0x02, 0x02, 0x02, 0x02, 0x02, 0x02,
            };
            state.set_code(SENDER, code);
        }
        MONAD_ASSERT(bs.can_merge(state));
        bs.merge(state);
    }

    uint256_t const gas_fee = uint256_t{gas_fee_mon} * 1000000000000000000ULL;
    uint256_t const gas_limit = gas_fee / BASE_FEE_PER_GAS;
    MONAD_ASSERT(
        (gas_fee % BASE_FEE_PER_GAS) == 0 &&
        gas_limit <= std::numeric_limits<uint64_t>::max());

    Transaction const tx{
        .max_fee_per_gas = BASE_FEE_PER_GAS,
        .gas_limit = uint64_t{gas_limit},
        .type = TransactionType::legacy,
        .max_priority_fee_per_gas = 0,
    };

    std::vector<Address> senders;
    if (prevent_dip_bitset & (1 << SenderInBlock)) {
        senders.push_back(SENDER);
    }
    else {
        senders.push_back(Address{2});
    }
    senders.emplace_back(SENDER);
    std::vector<std::vector<std::optional<Address>>> authorities = {};
    if (prevent_dip_bitset & (1 << AuthorityInBlock)) {
        authorities.push_back({SENDER});
    }
    else {
        authorities.push_back({});
    }
    if (prevent_dip_bitset & (1 << AuthorityInTransaction)) {
        authorities.push_back({SENDER});
    }
    else {
        authorities.push_back({});
    }

    // Create sets for the new MonadChainContext structure
    ankerl::unordered_dense::segmented_set<Address>
        grandparent_senders_and_authorities;
    if (prevent_dip_bitset & (1 << SenderOrAuthorityInGrandparent)) {
        grandparent_senders_and_authorities.insert(SENDER);
    }
    ankerl::unordered_dense::segmented_set<Address>
        parent_senders_and_authorities;
    if (prevent_dip_bitset & (1 << SenderOrAuthorityInParent)) {
        parent_senders_and_authorities.insert(SENDER);
    }
    ankerl::unordered_dense::segmented_set<Address> const
        senders_and_authorities = {SENDER};

    MonadChainContext chain_context{
        .grandparent_senders_and_authorities =
            &grandparent_senders_and_authorities,
        .parent_senders_and_authorities = &parent_senders_and_authorities,
        .senders_and_authorities = senders_and_authorities,
        .senders = senders,
        .authorities = authorities};

    {
        State state{bs, Incarnation{1, 1}};
        state.subtract_from_balance(SENDER, gas_fee);
        uint256_t const value = uint256_t{value_mon} * 1000000000000000000ULL;
        state.subtract_from_balance(SENDER, value);
        bool should_revert = chain.revert_transaction(
            1, // block_number
            0, // timestamp
            SENDER,
            tx,
            BASE_FEE_PER_GAS,
            1, // transaction index
            state,
            chain_context);

        EXPECT_EQ(should_revert, expected)
            << std::bitset<64>{prevent_dip_bitset};
    }
}

TEST(MonadChain, revert_transaction_no_dip_gas_fee_with_no_value_false)
{
    for (uint8_t i = 1; i < PREVENT_DIP_BITS_POWERSET_SIZE; ++i) {
        run_revert_transaction_test(
            i, // prevent_dip_bitset
            10, // initial balance (MON)
            2, // gas fee (MON)
            0, // value (MON)
            false // expected should_revert
        );

        // now spend whole reserve
        run_revert_transaction_test(
            i, // prevent_dip_bitset
            10, // initial balance (MON)
            10, // gas fee (MON)
            0, // value (MON)
            false // expected should_revert
        );
    }
}

TEST(MonadChain, revert_transaction_no_dip_gas_fee_with_value_true)
{
    for (uint8_t i = 1; i < PREVENT_DIP_BITS_POWERSET_SIZE; ++i) {
        run_revert_transaction_test(
            i, // prevent_dip_bitset
            10, // initial balance (MON)
            2, // gas fee (MON)
            1, // value (MON)
            true // expected should_revert
        );

        run_revert_transaction_test(
            i, // prevent_dip_bitset
            15, // initial balance (MON)
            5, // gas fee (MON)
            6, // value (MON)
            true // expected should_revert
        );
    }
}

TEST(MonadChain, revert_transaction_no_dip_gas_fee_with_value_false)
{
    for (uint8_t i = 1; i < PREVENT_DIP_BITS_POWERSET_SIZE; ++i) {
        run_revert_transaction_test(
            i, // prevent_dip_bitset
            15, // initial balance (MON)
            5, // gas fee (MON)
            5, // value (MON)
            false // expected should_revert
        );
    }
}

TEST(MonadChain, revert_transaction_dip_false)
{
    run_revert_transaction_test(
        0, // prevent_dip_bitset
        10, // initial balance (MON)
        10, // gas fee (MON)
        0, // value (MON)
        false // expected should_revert
    );

    run_revert_transaction_test(
        0, // prevent_dip_bitset
        10, // initial balance (MON)
        1, // gas fee (MON)
        9, // value (MON)
        false // expected should_revert
    );
}

TEST(MonadChain, can_sender_dip_into_reserve)
{
    // False because of pending txns
    {
        std::vector<Address> const senders = {{Address{1}, Address{1}}};
        std::vector<std::vector<std::optional<Address>>> const authorities = {
            {}, {}};
        ankerl::unordered_dense::segmented_set<Address> const
            senders_and_authorities{{Address{1}}};
        MonadChainContext const context{
            .grandparent_senders_and_authorities = nullptr,
            .parent_senders_and_authorities = nullptr,
            .senders_and_authorities = senders_and_authorities,
            .senders = senders,
            .authorities = authorities,
        };
        EXPECT_FALSE(
            can_sender_dip_into_reserve(Address{1}, 1, NULL_HASH, context));
    }

    // False because of authority
    {
        std::vector<Address> const senders = {{Address{2}, Address{1}}};
        std::vector<std::vector<std::optional<Address>>> const authorities = {
            {}, {Address{1}}};
        ankerl::unordered_dense::segmented_set<Address> const
            senders_and_authorities{{Address{1}}};
        MonadChainContext const context{
            .grandparent_senders_and_authorities = nullptr,
            .parent_senders_and_authorities = nullptr,
            .senders_and_authorities = senders_and_authorities,
            .senders = senders,
            .authorities = authorities,
        };
        EXPECT_FALSE(
            can_sender_dip_into_reserve(Address{1}, 1, NULL_HASH, context));
    }
}

TEST(MonadChain, system_transaction_sender_is_authority)
{
    InMemoryMachine machine;
    mpt::Db db{machine};
    TrieDb tdb{db};
    vm::VM vm;
    BlockState bs{tdb, vm};
    State state{bs, Incarnation{0, 0}};
    std::vector<std::optional<Address>> const authorities = {SYSTEM_SENDER};

    {
        MonadDevnet chain;
        auto const res =
            chain.validate_transaction(0, 0, {}, {}, state, 0, authorities);
        ASSERT_TRUE(res.has_error());
        EXPECT_EQ(
            res.error(),
            MonadTransactionError::SystemTransactionSenderIsAuthority);
    }
}
