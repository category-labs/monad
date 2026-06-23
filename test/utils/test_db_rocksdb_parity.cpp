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

#include <gtest/gtest.h>

#ifdef MONAD_HAVE_ROCKSDB

    #include <test/utils/db_parity_harness.hpp>

    #include <category/async/util.hpp>
    #include <category/core/address.hpp>
    #include <category/core/assert.h>
    #include <category/core/byte_string.hpp>
    #include <category/core/bytes.hpp>
    #include <category/core/keccak.hpp>
    #include <category/execution/ethereum/core/account.hpp>
    #include <category/execution/ethereum/core/block.hpp>
    #include <category/execution/ethereum/db/db.hpp>
    #include <category/execution/ethereum/db/rocksdb_db.hpp>
    #include <category/execution/ethereum/db/test/commit_simple.hpp>
    #include <category/execution/ethereum/db/trie_db.hpp>
    #include <category/execution/ethereum/db/util.hpp>
    #include <category/execution/ethereum/state2/state_deltas.hpp>
    #include <category/execution/ethereum/types/incarnation.hpp>
    #include <category/mpt/db.hpp>
    #include <category/vm/code.hpp>

    #include <cstdint>
    #include <filesystem>
    #include <memory>
    #include <string>
    #include <vector>

using namespace monad;
using namespace monad::test;

namespace
{
    struct TempDir
    {
        std::filesystem::path path;

        TempDir()
        {
            std::filesystem::path tmpl =
                MONAD_ASYNC_NAMESPACE::working_temporary_directory() /
                "monad_rocksdb_parity_XXXXXX";
            char *const result = ::mkdtemp((char *)tmpl.native().data());
            MONAD_ASSERT(result != nullptr);
            path = result;
        }

        TempDir(TempDir const &) = delete;
        TempDir &operator=(TempDir const &) = delete;

        ~TempDir()
        {
            std::error_code ec;
            std::filesystem::remove_all(path, ec);
        }
    };

    Address addr(uint64_t const i)
    {
        return Address{i};
    }

    StorageDelta ins(uint64_t const v)
    {
        return StorageDelta{bytes32_t{}, bytes32_t{v}};
    }

    StorageDelta del(uint64_t const old_v)
    {
        return StorageDelta{bytes32_t{old_v}, bytes32_t{}};
    }

    void commit_block(
        Db &db, uint64_t const number, std::unique_ptr<StateDeltas> deltas,
        Code const &code = {})
    {
        BlockHeader const header{.number = number};
        bytes32_t const block_id{number}; // number >= 1 => non-empty block id
        commit_simple(db, std::move(deltas), code, block_id, header);
        db.finalize(number, block_id);
        db.set_block_and_prefix(number);
    }

    std::string report(BlockParity const &b)
    {
        std::string s;
        for (std::string const &m : b.mismatches) {
            s += "\n  " + m;
        }
        return s;
    }
}

// Drive an in-memory MonadDB (reference) and a RocksDbDb (candidate) through an
// identical block stream and require all four roots plus sampled reads to agree
// after every block. The scenario deliberately exercises the on-disk witness
// walk: trie branching across many keys, storage upserts/clears, account
// deletion (branch compression), an incarnation bump (storage wipe + rebuild),
// and contract code.
TEST(RocksDbParity, matches_monaddb_across_blocks)
{
    mpt::Db ref_db{std::make_unique<InMemoryMachine>()};
    TrieDb reference{ref_db};

    TempDir const rocksdb_dir;
    RocksDbDb candidate{rocksdb_dir.path};

    DbParityHarness harness{reference, candidate, "monaddb", "rocksdb"};

    // Sample a spread of keys touched across the scenario.
    std::vector<SampledKey> sampled;
    for (uint64_t i = 0; i < 40; ++i) {
        sampled.push_back(SampledKey::account_of(addr(i)));
    }
    sampled.push_back(
        SampledKey::storage_of(addr(2), Incarnation{0, 0}, bytes32_t{1}));
    sampled.push_back(
        SampledKey::storage_of(addr(2), Incarnation{0, 0}, bytes32_t{2}));

    // Block 1: insert 40 accounts (forces a branching account trie); a few
    // carry storage.
    auto const blk1 = harness.on_block(
        1,
        [](Db &db) {
            StateDeltas d;
            for (uint64_t i = 0; i < 40; ++i) {
                StorageDeltas storage;
                if (i == 2) {
                    storage.emplace(bytes32_t{1}, ins(0x11));
                    storage.emplace(bytes32_t{2}, ins(0x22));
                    storage.emplace(bytes32_t{3}, ins(0x33));
                }
                d.emplace(
                    addr(i),
                    StateDelta{
                        .account =
                            {std::nullopt,
                             Account{.balance = i + 1, .nonce = i + 1}},
                        .storage = storage});
            }
            commit_block(db, 1, std::make_unique<StateDeltas>(std::move(d)));
        },
        sampled);
    EXPECT_TRUE(blk1.match()) << report(blk1);

    // Block 2: update some balances, add and clear storage slots on addr(2).
    auto const blk2 = harness.on_block(
        2,
        [](Db &db) {
            StateDeltas d;
            StorageDeltas storage;
            storage.emplace(bytes32_t{2}, del(0x22)); // clear an existing slot
            storage.emplace(bytes32_t{4}, ins(0x44)); // add a new slot
            d.emplace(
                addr(2),
                StateDelta{
                    .account =
                        {Account{.balance = 3, .nonce = 3},
                         Account{.balance = 300, .nonce = 4}},
                    .storage = storage});
            d.emplace(
                addr(7),
                StateDelta{
                    .account = {
                        Account{.balance = 8, .nonce = 8},
                        Account{.balance = 800, .nonce = 9}}});
            commit_block(db, 2, std::make_unique<StateDeltas>(std::move(d)));
        },
        sampled);
    EXPECT_TRUE(blk2.match()) << report(blk2);

    // Block 3: delete a swath of accounts (triggers branch compression in the
    // account trie -> exercises the witness's branch-completeness).
    auto const blk3 = harness.on_block(
        3,
        [](Db &db) {
            StateDeltas d;
            for (uint64_t i = 20; i < 40; ++i) {
                d.emplace(
                    addr(i),
                    StateDelta{
                        .account = {
                            Account{.balance = i + 1, .nonce = i + 1},
                            std::nullopt}});
            }
            commit_block(db, 3, std::make_unique<StateDeltas>(std::move(d)));
        },
        sampled);
    EXPECT_TRUE(blk3.match()) << report(blk3);

    // Block 4: deploy a contract (new code) at a fresh address.
    byte_string const code_bytes(64, 0xfe);
    bytes32_t const code_hash =
        to_bytes(keccak256({code_bytes.data(), code_bytes.size()}));
    std::vector<SampledKey> sampled4{sampled};
    sampled4.push_back(SampledKey::code_of(code_hash));
    auto const blk4 = harness.on_block(
        4,
        [&](Db &db) {
            Code code;
            code.emplace(
                code_hash,
                vm::make_shared_intercode(std::span<uint8_t const>{
                    code_bytes.data(), code_bytes.size()}));
            StateDeltas d;
            d.emplace(
                addr(100),
                StateDelta{
                    .account = {
                        std::nullopt,
                        Account{
                            .balance = 1,
                            .code_hash = code_hash,
                            .nonce = 1}}});
            commit_block(
                db, 4, std::make_unique<StateDeltas>(std::move(d)), code);
        },
        sampled4);
    EXPECT_TRUE(blk4.match()) << report(blk4);

    // Block 5: incarnation bump on addr(2) (selfdestruct + recreate) -> the old
    // storage trie is wiped and rebuilt from this block's slot deltas. Sample
    // the new incarnation's storage: real execution always reads with the live
    // incarnation, so the dead inc-0 slots (still present in the flat store, by
    // design) are never observed.
    std::vector<SampledKey> sampled5;
    for (uint64_t i = 0; i < 40; ++i) {
        sampled5.push_back(SampledKey::account_of(addr(i)));
    }
    sampled5.push_back(
        SampledKey::storage_of(addr(2), Incarnation{5, 0}, bytes32_t{9}));
    sampled5.push_back(
        SampledKey::storage_of(addr(2), Incarnation{5, 0}, bytes32_t{1}));
    auto const blk5 = harness.on_block(
        5,
        [](Db &db) {
            StateDeltas d;
            StorageDeltas storage;
            storage.emplace(bytes32_t{9}, ins(0x99));
            d.emplace(
                addr(2),
                StateDelta{
                    .account =
                        {Account{
                             .balance = 300,
                             .nonce = 4,
                             .incarnation = Incarnation{0, 0}},
                         Account{
                             .balance = 5,
                             .nonce = 1,
                             .incarnation = Incarnation{5, 0}}},
                    .storage = storage});
            commit_block(db, 5, std::make_unique<StateDeltas>(std::move(d)));
        },
        sampled5);
    EXPECT_TRUE(blk5.match()) << report(blk5);

    EXPECT_EQ(harness.blocks(), 5u);
    EXPECT_EQ(harness.mismatched_blocks(), 0u);
    EXPECT_TRUE(harness.ok());

    // The candidate's persisted root must equal the reference's.
    EXPECT_EQ(candidate.state_root(), reference.state_root());
}

#else

TEST(RocksDbParity, SkippedWithoutRocksDb)
{
    GTEST_SKIP() << "requires -DMONAD_ENABLE_ROCKSDB=ON";
}

#endif // MONAD_HAVE_ROCKSDB
