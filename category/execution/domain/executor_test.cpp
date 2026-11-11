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

#include <category/async/config.hpp>
#include <category/async/util.hpp>
#include <category/core/address.hpp>
#include <category/core/assert.h>
#include <category/core/byte_string.hpp>
#include <category/core/bytes.hpp>
#include <category/core/fiber/priority_pool.hpp>
#include <category/core/hex.hpp>
#include <category/core/keccak.hpp>
#include <category/execution/domain/chain_id.hpp>
#include <category/execution/domain/derive_domain_block.hpp>
#include <category/execution/domain/executor.hpp>
#include <category/execution/domain/system_transaction.hpp>
#include <category/execution/ethereum/chain/genesis_state.hpp>
#include <category/execution/ethereum/core/block.hpp>
#include <category/execution/ethereum/core/rlp/block_rlp.hpp>
#include <category/execution/ethereum/core/rlp/transaction_rlp.hpp>
#include <category/execution/ethereum/core/transaction.hpp>
#include <category/execution/ethereum/db/ordered_trie.hpp>
#include <category/execution/ethereum/db/trie_db.hpp>
#include <category/execution/ethereum/db/util.hpp>
#include <category/execution/monad/chain/monad_chain.hpp>
#include <category/mpt/db.hpp>
#include <category/mpt/nibbles_view.hpp>
#include <category/mpt/ondisk_db_config.hpp>
#include <category/vm/evm/monad/revision.h>
#include <category/vm/evm/traits.hpp>
#include <category/vm/vm.hpp>

#include <gtest/gtest.h>

#include <cstdint>
#include <filesystem>
#include <memory>
#include <optional>
#include <string>
#include <utility>
#include <vector>

#include <fcntl.h>
#include <unistd.h>

using namespace monad;
using namespace monad::domain;
using namespace monad::literals;

namespace
{
    constexpr uint64_t DOMAIN = 0x510000004eaf;
    constexpr monad_revision REVISION = MONAD_TEN;
    constexpr Address SPOKE =
        0x5FbDB2315678afecb367f032d93F642f64180aa3_address;
    // Signs the transaction below.
    constexpr Address SENDER =
        0x6f4c950442e1Af093BcfF730381E63Ae9171b87a_address;

    // An EIP-1559 transaction of DOMAIN (nonce 0, gas 100'000, to 0xabc,
    // data 0x0102) signed by secp256k1 key 0x42, by eth-account.
    Transaction signed_transaction()
    {
        auto const encoded = *from_hex(
            "02f87086510000004eaf8080850ba43b7400830186a094000000000000000000"
            "0000000000000000000abc80820102c080a03524410eec196ed020b64c6e2b16"
            "b18249621686c02655d096b510644ee71a27a05400ac6a0ec2d6bee704ab7aff"
            "e172fe9b86521a26d164b21bc8966dc9569f05");
        byte_string_view view{encoded};
        return rlp::decode_transaction(view).value();
    }

    Transaction delivery(uint64_t const nonce)
    {
        return make_domain_system_transaction(
            DOMAIN,
            SPOKE,
            DOMAIN_GAS_PRICE,
            300'000,
            DOMAIN & NETWORK_CHAIN_ID_MASK,
            Address{0x1111},
            Address{0x2222},
            byte_string{0xca, 0xfe},
            nonce);
    }

    // The block derivation would hand on: senders as it recovers them.
    DerivedDomainBlock
    block(uint64_t const number, std::vector<Transaction> txs)
    {
        std::vector<Address> senders;
        for (auto const &tx : txs) {
            auto const sender = recover_sender(tx);
            MONAD_ASSERT(sender.has_value());
            senders.push_back(*sender);
        }
        return DerivedDomainBlock{
            .number = number,
            .l1_block_number = 10 + number,
            .timestamp = 1'000 + number,
            .prev_randao = bytes32_t{0x77},
            .transactions = std::move(txs),
            .senders = std::move(senders)};
    }

    bytes32_t transactions_root(DerivedDomainBlock const &block)
    {
        std::vector<byte_string> encoded;
        for (auto const &tx : block.transactions) {
            encoded.push_back(rlp::encode_transaction(tx));
        }
        return ordered_trie_root(encoded);
    }

    struct TestL1Chain final : MonadChain
    {
        uint256_t get_chain_id() const override
        {
            return DOMAIN & NETWORK_CHAIN_ID_MASK;
        }

        monad_revision get_monad_revision(uint64_t) const override
        {
            return REVISION;
        }

        GenesisState get_genesis_state() const override
        {
            return GenesisState{};
        }
    };

    bytes32_t compute_block_hash(BlockHeader const &header)
    {
        return to_bytes(keccak256(rlp::encode_block_header(header)));
    }

    class PrivateDomainExecutorTest : public ::testing::Test
    {
    protected:
        std::filesystem::path dir_;
        std::string db_path_;
        std::optional<mpt::Db> db_;
        std::vector<DerivedDomainBlock> blocks_;
        TestL1Chain l1_chain_;
        vm::VM vm_;
        fiber::PriorityPool pool_{1, 1};

        void SetUp() override
        {
            std::string pattern =
                (MONAD_ASYNC_NAMESPACE::working_temporary_directory() /
                 "private_domain_executor_XXXXXX")
                    .string();
            ASSERT_NE(::mkdtemp(pattern.data()), nullptr);
            dir_ = pattern;
            db_path_ = (dir_ / "domain.db").string();
            {
                int const fd = ::open(
                    db_path_.c_str(), O_CREAT | O_WRONLY | O_CLOEXEC, 0644);
                ASSERT_NE(fd, -1);
                ASSERT_NE(
                    ::ftruncate(
                        fd, static_cast<off_t>(8ULL * 1024 * 1024 * 1024)),
                    -1);
                ::close(fd);
            }
            open_db(false);
        }

        void TearDown() override
        {
            db_.reset();
            std::filesystem::remove_all(dir_);
        }

        void open_db(bool const append)
        {
            db_.reset();
            std::unique_ptr<mpt::StateMachine> machine;
            if (mip_8_active(REVISION)) {
                machine = std::make_unique<MonadOnDiskMachine>();
            }
            else {
                machine = std::make_unique<OnDiskMachine>();
            }
            db_.emplace(
                std::move(machine),
                mpt::OnDiskDbConfig{
                    .append = append,
                    .dbname_path = db_path_,
                    .chunk_capacity = 24});
        }

        // Derives a block with these transactions after the last one.
        void append(std::vector<Transaction> txs)
        {
            blocks_.push_back(block(
                blocks_.empty() ? 0 : blocks_.back().number + 1,
                std::move(txs)));
        }

        // Hands the executor every derived block from its next one on.
        void execute_all(PrivateDomainExecutor &executor)
        {
            for (auto number = executor.next_block(); number < blocks_.size();
                 ++number) {
                EXPECT_TRUE(executor.execute(blocks_[number]).has_value());
            }
        }

        // The header of finalized block `number` of the domain's db.
        BlockHeader read_domain_header(uint64_t const number)
        {
            auto const cursor = db_->find(
                mpt::concat(
                    FINALIZED_NIBBLE, mpt::NibblesView{block_header_nibbles}),
                number);
            MONAD_ASSERT(cursor.has_value());
            byte_string_view encoded{cursor.value().node->value()};
            auto header = rlp::decode_block_header(encoded);
            MONAD_ASSERT(header.has_value());
            return std::move(header).value();
        }

        std::vector<uint64_t> statuses(uint64_t const number)
        {
            std::vector<uint64_t> result;
            auto const receipts = get_receipts(*db_, number);
            MONAD_ASSERT(receipts.has_value());
            for (auto const &receipt : receipts.value()) {
                result.push_back(receipt.status);
            }
            return result;
        }

        std::optional<Account> account(Address const &address)
        {
            TrieDb db{*db_};
            return db.read_account(address);
        }
    };
}

TEST_F(PrivateDomainExecutorTest, executes_blocks_in_order)
{
    append({});
    append({signed_transaction()});
    // The second transaction fails validation on its nonce and keeps its
    // place with a status-0 receipt.
    append({delivery(0), signed_transaction()});

    PrivateDomainExecutor executor{l1_chain_, DOMAIN, *db_, vm_, pool_};
    EXPECT_EQ(executor.next_block(), 0);
    execute_all(executor);
    EXPECT_EQ(executor.next_block(), 3);
    EXPECT_EQ(db_->get_latest_finalized_version(), 2);

    auto const genesis = read_domain_header(0);
    auto const first = read_domain_header(1);
    auto const second = read_domain_header(2);
    EXPECT_EQ(genesis.parent_hash, bytes32_t{});
    EXPECT_EQ(first.parent_hash, compute_block_hash(genesis));
    EXPECT_EQ(second.parent_hash, compute_block_hash(first));
    EXPECT_EQ(first.number, 1);
    EXPECT_EQ(first.timestamp, 1'001);
    EXPECT_EQ(first.beneficiary, Address{});
    EXPECT_EQ(second.transactions_root, transactions_root(blocks_[2]));
    EXPECT_NE(first.state_root, genesis.state_root);
    EXPECT_EQ(statuses(1), (std::vector<uint64_t>{1}));
    EXPECT_EQ(statuses(2), (std::vector<uint64_t>{1, 0}));
    EXPECT_EQ(second.gas_used, get_receipts(*db_, 2).value().back().gas_used);

    ASSERT_TRUE(account(SENDER).has_value());
    EXPECT_EQ(account(SENDER)->nonce, 1);
    EXPECT_EQ(account(SENDER)->balance, 0);
}

TEST_F(PrivateDomainExecutorTest, continues_after_a_restart)
{
    append({});
    append({signed_transaction()});
    {
        PrivateDomainExecutor executor{l1_chain_, DOMAIN, *db_, vm_, pool_};
        execute_all(executor);
    }
    auto const before = read_domain_header(1);

    open_db(true);
    append({});
    PrivateDomainExecutor executor{l1_chain_, DOMAIN, *db_, vm_, pool_};
    EXPECT_EQ(executor.next_block(), 2);
    execute_all(executor);
    EXPECT_EQ(executor.next_block(), 3);
    EXPECT_EQ(read_domain_header(1), before);
    EXPECT_EQ(read_domain_header(2).parent_hash, compute_block_hash(before));
    EXPECT_EQ(read_domain_header(2).state_root, before.state_root);
}
