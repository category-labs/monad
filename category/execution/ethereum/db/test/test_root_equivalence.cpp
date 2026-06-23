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

// F7 root-equivalence (linchpin): the RocksDB-side state-root computation must
// match MonadDB. PartialTrieDb is the content-addressed (node_hash-keyed,
// canonical-RLP) trie the RocksDB backend's CF_TRIE_NODES codec is built on;
// this test drives the SAME StateDeltas through PartialTrieDb (built from an
// empty witness) and an in-memory MonadDB TrieDb, and asserts their state roots
// agree block-for-block. Both must equal the canonical Ethereum state root, so
// a mismatch is a real bug in one side's handling of the divergence-prone
// cases: account deletion, incarnation bumps (selfdestruct+recreate), and
// storage clears. v1 covers the state root; receipts/transactions/withdrawals
// roots are validated via the existing MonadDB-vs-MonadDB path (F3).

#include <category/core/assert.h>
#include <category/core/bytes.hpp>
#include <category/execution/ethereum/core/account.hpp>
#include <category/execution/ethereum/core/block.hpp>
#include <category/execution/ethereum/db/commit_builder.hpp>
#include <category/execution/ethereum/db/partial_trie_db.hpp>
#include <category/execution/ethereum/db/trie_db.hpp>
#include <category/execution/ethereum/db/util.hpp>
#include <category/execution/ethereum/state2/state_deltas.hpp>
#include <category/execution/ethereum/types/incarnation.hpp>
#include <category/mpt/db.hpp>

#include <test_resource_data.h> // monad::test::commit_sequential

#include <gtest/gtest.h>

#include <algorithm>
#include <cstdint>
#include <map>
#include <memory>
#include <numeric>
#include <optional>
#include <random>
#include <string>
#include <vector>

using namespace monad;
using namespace monad::test;

namespace
{
    Account make_account(
        uint64_t const nonce, uint64_t const balance,
        unsigned char const code_tag, Incarnation const incarnation)
    {
        Account a{};
        a.nonce = nonce;
        a.balance = balance;
        a.incarnation = incarnation;
        // code_hash is just a 32-byte field in the leaf; a distinct tag is
        // enough to exercise the state root (the code itself lives elsewhere).
        bytes32_t h{};
        h.bytes[0] = code_tag;
        a.code_hash = h;
        return a;
    }

    bytes32_t b32(uint64_t const v)
    {
        return bytes32_t{v};
    }

    std::string hex(bytes32_t const &b)
    {
        static constexpr char digits[] = "0123456789abcdef";
        std::string s{"0x"};
        for (unsigned char const c : b.bytes) {
            s += digits[c >> 4];
            s += digits[c & 0x0f];
        }
        return s;
    }

    StateDelta account_delta(
        std::optional<Account> const &before,
        std::optional<Account> const &after)
    {
        return StateDelta{.account = {before, after}};
    }

    PartialTrieDb empty_partial()
    {
        auto result = PartialTrieDb::from_witness(NULL_ROOT, {}, {});
        MONAD_ASSERT(!result.has_error());
        return std::move(result.value());
    }

    // Drives the same block of deltas through PartialTrieDb (RocksDB-side
    // codec) and an in-memory MonadDB TrieDb (oracle), then compares state
    // roots.
    class RootEquivalence
    {
    public:
        RootEquivalence()
            : mona_mpt_{std::make_unique<InMemoryMachine>()}
            , mona_{mona_mpt_}
            , partial_{empty_partial()}
        {
        }

        ::testing::AssertionResult commit_block(StateDeltas const &deltas)
        {
            ++block_;
            BlockHeader const header{.number = block_};

            // MonadDB oracle: commit + finalize + position at finalized.
            commit_sequential(
                mona_, std::make_unique<StateDeltas>(deltas), Code{}, header);

            // RocksDB-side: PartialTrieDb commit (witness/zkVM context uses an
            // empty block_id).
            CommitBuilder builder{header.number};
            partial_.commit(
                bytes32_t{},
                builder,
                header,
                std::make_unique<StateDeltas>(deltas),
                [](BlockHeader &) {});

            auto const oracle = mona_.state_root();
            auto const candidate = partial_.state_root();
            if (oracle != candidate) {
                return ::testing::AssertionFailure()
                       << "state_root diverged at block " << block_
                       << ": monaddb=" << hex(oracle)
                       << " partial=" << hex(candidate);
            }
            return ::testing::AssertionSuccess();
        }

    private:
        mpt::Db mona_mpt_;
        TrieDb mona_;
        PartialTrieDb partial_;
        uint64_t block_{0};
    };
}

TEST(RootEquivalence, create_update_delete_recreate)
{
    RootEquivalence eq;
    Address const a{0x1001};
    Address const b{0x1002};

    // Block 1: create two accounts, one with storage.
    {
        StateDelta da = account_delta(
            std::nullopt, make_account(1, 100, 0xaa, Incarnation{1, 0}));
        da.storage.emplace(b32(1), StorageDelta{bytes32_t{}, b32(0x42)});
        da.storage.emplace(b32(2), StorageDelta{bytes32_t{}, b32(0x43)});
        StateDeltas d;
        d.emplace(a, da);
        d.emplace(
            b,
            account_delta(
                std::nullopt, make_account(0, 7, 0xbb, Incarnation{1, 1})));
        EXPECT_TRUE(eq.commit_block(d));
    }

    // Block 2: update a, clear one of its slots, delete b.
    {
        StateDelta da = account_delta(
            make_account(1, 100, 0xaa, Incarnation{1, 0}),
            make_account(2, 250, 0xaa, Incarnation{1, 0}));
        da.storage.emplace(b32(1), StorageDelta{b32(0x42), bytes32_t{}});
        StateDeltas d;
        d.emplace(a, da);
        d.emplace(
            b,
            account_delta(
                make_account(0, 7, 0xbb, Incarnation{1, 1}), std::nullopt));
        EXPECT_TRUE(eq.commit_block(d));
    }

    // Block 3: recreate b at a bumped incarnation with fresh storage
    // (selfdestruct+recreate semantics).
    {
        StateDelta db = account_delta(
            std::nullopt, make_account(0, 9, 0xcc, Incarnation{3, 0}));
        db.storage.emplace(b32(5), StorageDelta{bytes32_t{}, b32(0x99)});
        StateDeltas d;
        d.emplace(b, db);
        EXPECT_TRUE(eq.commit_block(d));
    }
}

// Seeded, model-tracked random blocks exercising creates/updates/deletes,
// storage writes/clears, and incarnation bumps. Each block touches a set of
// DISTINCT addresses (tbb concurrent_hash_map has no overwrite-insert), and the
// tracked model yields correct before-values since both backends evolve from
// identical deltas.
TEST(RootEquivalence, randomized_fuzz)
{
    RootEquivalence eq;
    std::mt19937_64 rng{0xF7F7F7};

    struct Model
    {
        Account account;
        std::map<bytes32_t, bytes32_t> storage;
    };

    std::map<Address, Model> state;

    constexpr unsigned kAddrs = 8;
    constexpr unsigned kSlots = 6;
    auto const addr = [](unsigned const i) { return Address{0x2000 + i}; };

    for (unsigned blk = 0; blk < 80; ++blk) {
        std::vector<unsigned> idx(kAddrs);
        std::iota(idx.begin(), idx.end(), 0u);
        std::shuffle(idx.begin(), idx.end(), rng);

        unsigned const ops = 1 + static_cast<unsigned>(rng() % 4);
        StateDeltas d;
        for (unsigned k = 0; k < ops; ++k) {
            Address const ad = addr(idx[k]);
            auto const it = state.find(ad);
            bool const exists = it != state.end();
            unsigned const choice = static_cast<unsigned>(rng() % 10);

            if (!exists) {
                Account const acct = make_account(
                    1,
                    rng() % 1000,
                    static_cast<unsigned char>(rng()),
                    Incarnation{blk + 1, k});
                StateDelta da = account_delta(std::nullopt, acct);
                Model m{.account = acct, .storage = {}};
                if (rng() % 2) {
                    bytes32_t const slot = b32(rng() % kSlots);
                    bytes32_t const val = b32(1 + (rng() % 0xffff));
                    da.storage.emplace(slot, StorageDelta{bytes32_t{}, val});
                    m.storage[slot] = val;
                }
                d.emplace(ad, da);
                state[ad] = m;
            }
            else if (choice < 2) {
                d.emplace(ad, account_delta(it->second.account, std::nullopt));
                state.erase(it);
            }
            else if (choice < 4) {
                Account const acct = make_account(
                    1,
                    rng() % 1000,
                    static_cast<unsigned char>(rng()),
                    Incarnation{blk + 1, k});
                d.emplace(ad, account_delta(it->second.account, acct));
                state[ad] = Model{.account = acct, .storage = {}};
            }
            else {
                Account next = it->second.account;
                next.nonce += 1;
                next.balance = next.balance + 1;
                StateDelta da = account_delta(it->second.account, next);
                bytes32_t const slot = b32(rng() % kSlots);
                auto const sit = it->second.storage.find(slot);
                bytes32_t const old = (sit != it->second.storage.end())
                                          ? sit->second
                                          : bytes32_t{};
                bytes32_t const val =
                    (rng() % 4 == 0) ? bytes32_t{} : b32(1 + (rng() % 0xffff));
                da.storage.emplace(slot, StorageDelta{old, val});
                d.emplace(ad, da);
                it->second.account = next;
                if (val == bytes32_t{}) {
                    it->second.storage.erase(slot);
                }
                else {
                    it->second.storage[slot] = val;
                }
            }
        }
        if (!d.empty()) {
            ASSERT_TRUE(eq.commit_block(d)) << "fuzz block " << blk;
        }
    }
}
