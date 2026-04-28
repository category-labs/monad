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

// End to end test for the slot to page storage migration. Drives the
// shared monad::commit_block helper used by cmd/monad/runloop_monad.cpp:
// pre fork the Db1 (slot encoded) state_root is stamped into the canonical
// header; post fork the Db2 (page encoded) state_root is stamped instead.
// Both Db1 and Db2 receive the same block header.

#include <category/core/address.hpp>
#include <category/core/bytes.hpp>
#include <category/execution/ethereum/core/block.hpp>
#include <category/execution/ethereum/core/receipt.hpp>
#include <category/execution/ethereum/core/transaction.hpp>
#include <category/execution/ethereum/core/withdrawal.hpp>
#include <category/execution/ethereum/db/db.hpp>
#include <category/execution/ethereum/db/trie_db.hpp>
#include <category/execution/ethereum/db/util.hpp>
#include <category/execution/ethereum/state2/state_deltas.hpp>
#include <category/execution/ethereum/trace/call_frame.hpp>
#include <category/execution/ethereum/types/incarnation.hpp>
#include <category/execution/monad/db/commit_block_migration.hpp>
#include <category/execution/monad/db/page_storage_broker.hpp>
#include <category/execution/monad/db/storage_page.hpp>
#include <category/mpt/db.hpp>
#include <category/mpt/ondisk_db_config.hpp>
#include <category/vm/evm/monad/revision.h>
#include <category/vm/evm/traits.hpp>

#include <gtest/gtest.h>

#include <test_resource_data.h>

#include <cstdint>
#include <optional>
#include <vector>

using namespace monad;
using namespace monad::test;

namespace
{
    // Slots 0x00 and 0x01 share one page; slot 0x80 is on a different page.
    // This forces MonadCommitBuilder to merge two slot deltas onto the same
    // page within a single block, exercising the page grouping path.
    constexpr auto slot_0 = bytes32_t{uint64_t{0x00}};
    constexpr auto slot_1 = bytes32_t{uint64_t{0x01}};
    constexpr auto slot_far = bytes32_t{uint64_t{0x80}};

    bytes32_t make_val(uint64_t const v)
    {
        return bytes32_t{v};
    }

    // Empty ancillary buckets reused for every block: the test only cares
    // about state_deltas, so receipts/txns/etc. stay empty across calls.
    Code const empty_code{};
    std::vector<Receipt> const empty_receipts{};
    std::vector<Transaction> const empty_transactions{};
    std::vector<Address> const empty_senders{};
    std::vector<std::vector<CallFrame>> const empty_call_frames{};
    std::vector<BlockHeader> const empty_ommers{};
    std::optional<std::vector<Withdrawal>> const empty_withdrawals{};

    BlockCommitAncillaries make_empty_ancillaries()
    {
        return BlockCommitAncillaries{
            .code = empty_code,
            .receipts = empty_receipts,
            .transactions = empty_transactions,
            .senders = empty_senders,
            .call_frames = empty_call_frames,
            .ommers = empty_ommers,
            .withdrawals = empty_withdrawals};
    }

    // Drive monad::commit_block for one block, mirroring how the runloop
    // calls it. is_post_fork toggles which Monad revision (and therefore
    // which trait instantiation) is used. Pre fork blocks pick MONAD_ZERO,
    // which is < MONAD_NEXT, so primary commits first; post fork picks
    // MONAD_NEXT, so secondary commits first.
    void drive_commit(
        TrieDb &tdb1, TrieDb &tdb2, bool const is_post_fork,
        uint64_t const block_number, bytes32_t const &block_id,
        bytes32_t const &parent_id, bool const is_first,
        StateDeltas const &deltas)
    {
        // The runloop primes the primary db's prefix before execution; the
        // test does the same before driving commit_block. The helper takes
        // care of priming the secondary db's prefix internally. We start
        // from a fresh db so the parent prefix only exists from block 2
        // onwards.
        if (!is_first) {
            tdb1.set_block_and_prefix(block_number - 1, parent_id);
        }

        BlockHeader const header{.number = block_number};

        PageStorageBroker broker{tdb2};
        BlockCommitAncillaries const anc = make_empty_ancillaries();

        if (is_post_fork) {
            commit_block<MonadTraits<MONAD_NEXT>>(
                tdb1,
                tdb2,
                broker,
                block_id,
                parent_id,
                is_first,
                header,
                deltas,
                anc);
        }
        else {
            commit_block<MonadTraits<MONAD_ZERO>>(
                tdb1,
                tdb2,
                broker,
                block_id,
                parent_id,
                is_first,
                header,
                deltas,
                anc);
        }

        tdb1.finalize(block_number, block_id);
        tdb2.finalize(block_number, block_id);
    }

    StateDeltas make_deltas(
        std::optional<Account> const &prev_acct,
        std::optional<Account> const &new_acct,
        std::vector<std::tuple<bytes32_t, bytes32_t, bytes32_t>> const &slots)
    {
        StorageDeltas storage;
        for (auto const &[k, prev, next] : slots) {
            storage.emplace(k, StorageDelta{prev, next});
        }
        StateDeltas deltas;
        deltas.emplace(
            ADDR_A,
            StateDelta{
                .account = {prev_acct, new_acct},
                .storage = std::move(storage)});
        return deltas;
    }
}

TEST(MigrationFork, dual_write_state_root_handoff)
{
    ASSERT_EQ(compute_page_key(slot_0), compute_page_key(slot_1));
    ASSERT_NE(compute_page_key(slot_0), compute_page_key(slot_far));

    OnDiskMachine machine1;
    mpt::Db db1{machine1, mpt::OnDiskDbConfig{}};
    TrieDb tdb1{db1};

    MonadOnDiskMachine machine2;
    mpt::Db db2{machine2, mpt::OnDiskDbConfig{}};
    TrieDb tdb2{db2};

    auto const make_block_id = [](uint64_t const n) {
        return bytes32_t{n + 1};
    };

    // Three pre fork blocks, then two post fork. Acct lifetime: created at
    // block 1, mutated each block. Slots are seeded then updated.
    Account acct{.nonce = 1};
    bytes32_t prev_id{};

    // The canonical header populated by populate_header is the same lambda
    // for both Dbs in propose_block, so both Dbs end up with the same
    // header bytes. Pre fork the canonical state_root is Db1's; post fork
    // it is Db2's. These helpers express that invariant.
    auto check_pre_fork_headers = [&](char const *tag) {
        SCOPED_TRACE(tag);
        auto const h1 = tdb1.read_eth_header();
        auto const h2 = tdb2.read_eth_header();
        EXPECT_EQ(h1.state_root, h2.state_root)
            << "Db1 and Db2 must share the same canonical header";
        EXPECT_EQ(h1.state_root, tdb1.state_root())
            << "pre fork header carries Db1 (slot encoded) state_root";
        EXPECT_NE(tdb1.state_root(), tdb2.state_root())
            << "slot and page encodings should produce different roots";
    };
    auto check_post_fork_headers = [&](char const *tag) {
        SCOPED_TRACE(tag);
        auto const h1 = tdb1.read_eth_header();
        auto const h2 = tdb2.read_eth_header();
        EXPECT_EQ(h1.state_root, h2.state_root)
            << "Db1 and Db2 must share the same canonical header";
        EXPECT_EQ(h1.state_root, tdb2.state_root())
            << "post fork header carries Db2 (page encoded) state_root";
        EXPECT_NE(h1.state_root, tdb1.state_root())
            << "post fork header should not carry Db1 (slot) root";
    };

    // Block 1 (pre fork): create account, seed slot_0 and slot_1 (same page).
    {
        auto deltas = make_deltas(
            std::nullopt,
            acct,
            {{slot_0, bytes32_t{}, make_val(0xa1)},
             {slot_1, bytes32_t{}, make_val(0xb1)}});
        drive_commit(
            tdb1, tdb2, false, 1, make_block_id(1), prev_id, true, deltas);

        check_pre_fork_headers("block 1");

        PageStorageBroker br{tdb2};
        EXPECT_EQ(
            br.read_storage_slot(ADDR_A, Incarnation{0, 0}, slot_0),
            make_val(0xa1));
        EXPECT_EQ(
            br.read_storage_slot(ADDR_A, Incarnation{0, 0}, slot_1),
            make_val(0xb1));

        prev_id = make_block_id(1);
    }

    // Block 2 (pre fork): touch slot_0 and seed slot_far (different page).
    {
        auto next = acct;
        next.nonce = 2;
        auto deltas = make_deltas(
            acct,
            next,
            {{slot_0, make_val(0xa1), make_val(0xa2)},
             {slot_far, bytes32_t{}, make_val(0xfa)}});
        drive_commit(
            tdb1, tdb2, false, 2, make_block_id(2), prev_id, false, deltas);
        acct = next;

        check_pre_fork_headers("block 2");
        prev_id = make_block_id(2);
    }

    // Block 3 (pre fork): exercise repeated commits without storage churn.
    {
        auto next = acct;
        next.nonce = 3;
        auto deltas = make_deltas(acct, next, {});
        drive_commit(
            tdb1, tdb2, false, 3, make_block_id(3), prev_id, false, deltas);
        acct = next;

        check_pre_fork_headers("block 3");
        prev_id = make_block_id(3);
    }

    // Capture pre fork Db1 root for the boundary check below.
    bytes32_t const db1_root_pre_fork = tdb1.state_root();
    bytes32_t const db2_root_pre_fork = tdb2.state_root();
    ASSERT_NE(db1_root_pre_fork, bytes32_t{});
    ASSERT_NE(db2_root_pre_fork, bytes32_t{});

    // Block 4 (fork point, post fork): the canonical header now stamps
    // Db2's page based state_root. Db1's own state_root keeps advancing
    // (it still commits its slot encoded view) but the header points at
    // Db2's root.
    {
        auto next = acct;
        next.nonce = 4;
        auto deltas = make_deltas(
            acct,
            next,
            {{slot_1, make_val(0xb1), make_val(0xb4)}});
        drive_commit(
            tdb1, tdb2, true, 4, make_block_id(4), prev_id, false, deltas);
        acct = next;

        // Db1 advanced its slot encoded state root.
        EXPECT_NE(tdb1.state_root(), db1_root_pre_fork);
        EXPECT_NE(tdb1.state_root(), bytes32_t{});
        EXPECT_NE(tdb2.state_root(), db2_root_pre_fork);

        // Db1's stored header carries Db2's page based state root, and
        // Db2 sees the same header bytes.
        check_post_fork_headers("block 4 (fork)");

        prev_id = make_block_id(4);
    }

    // Block 5 (post fork): another post fork block reusing the same accounts
    // and a new slot value. Verifies the post fork path keeps working block
    // over block, not just at the fork boundary.
    {
        auto next = acct;
        next.nonce = 5;
        auto deltas = make_deltas(
            acct,
            next,
            {{slot_far, make_val(0xfa), make_val(0xf5)}});
        drive_commit(
            tdb1, tdb2, true, 5, make_block_id(5), prev_id, false, deltas);
        acct = next;

        check_post_fork_headers("block 5");

        PageStorageBroker br{tdb2};
        EXPECT_EQ(
            br.read_storage_slot(ADDR_A, Incarnation{0, 0}, slot_far),
            make_val(0xf5));
        EXPECT_EQ(
            br.read_storage_slot(ADDR_A, Incarnation{0, 0}, slot_1),
            make_val(0xb4));
        EXPECT_EQ(
            br.read_storage_slot(ADDR_A, Incarnation{0, 0}, slot_0),
            make_val(0xa2));
    }
}
