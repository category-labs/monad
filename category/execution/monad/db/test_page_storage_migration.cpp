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

#include <category/async/util.hpp>
#include <category/core/address.hpp>
#include <category/core/assert.h>
#include <category/core/bytes.hpp>
#include <category/execution/ethereum/chain/genesis_state.hpp>
#include <category/execution/ethereum/core/block.hpp>
#include <category/execution/ethereum/core/receipt.hpp>
#include <category/execution/ethereum/core/transaction.hpp>
#include <category/execution/ethereum/core/withdrawal.hpp>
#include <category/execution/ethereum/db/db.hpp>
#include <category/execution/ethereum/db/db_snapshot.h>
#include <category/execution/ethereum/db/db_snapshot_filesystem.h>
#include <category/execution/ethereum/db/trie_db.hpp>
#include <category/execution/ethereum/db/trie_rodb.hpp>
#include <category/execution/ethereum/db/util.hpp>
#include <category/execution/ethereum/state2/state_deltas.hpp>
#include <category/execution/ethereum/trace/call_frame.hpp>
#include <category/execution/ethereum/types/incarnation.hpp>
#include <category/execution/monad/chain/monad_testnet.hpp>
#include <category/execution/monad/db/commit_block_migration.hpp>
#include <category/execution/monad/db/state_machine_init.hpp>
#include <category/execution/monad/db/storage_page.hpp>
#include <category/mpt/db.hpp>
#include <category/mpt/ondisk_db_config.hpp>
#include <category/vm/evm/monad/revision.h>
#include <category/vm/evm/traits.hpp>

#include <gtest/gtest.h>

#include <test_resource_data.h>

#include <unistd.h>

#include <array>
#include <cstdint>
#include <filesystem>
#include <limits>
#include <optional>
#include <string>
#include <vector>

// End to end test for the slot to page storage migration. Drives the
// shared monad::commit_block helper used by cmd/monad/runloop_monad.cpp:
// pre fork the Db1 (slot encoded) state_root is stamped into the canonical
// header; post fork the Db2 (page encoded) state_root is stamped instead.
// Both Db1 and Db2 receive the same block header.

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

    enum class Fork
    {
        Pre,
        Post
    };

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
    // calls it. `fork` toggles which Monad revision (and therefore which
    // trait instantiation) is used: Fork::Pre picks MONAD_ZERO (primary
    // commits first), Fork::Post picks MONAD_NEXT (secondary commits first).
    void drive_commit(
        TrieDb &tdb1, TrieDb &tdb2, Fork const fork,
        uint64_t const block_number, bytes32_t const &block_id,
        StateDeltas const &deltas)
    {
        MONAD_ASSERT(!tdb1.is_page_encoded() && tdb2.is_page_encoded());
        BlockHeader const header{.number = block_number};
        BlockCommitAncillaries const anc = make_empty_ancillaries();

        if (fork == Fork::Post) {
            commit_block<MonadTraits<MONAD_NEXT>>(
                tdb1, &tdb2, block_id, header, deltas, anc);
        }
        else {
            commit_block<MonadTraits<MONAD_ZERO>>(
                tdb1, &tdb2, block_id, header, deltas, anc);
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

    // On-disk temp file sized for a small test DB (mirrors the mpt test
    // helper). Needed because promote/reopen requires a persistent backing
    // file to close and reopen against.
    std::filesystem::path make_temp_db_file(long const size_gb)
    {
        std::filesystem::path filename{
            MONAD_ASYNC_NAMESPACE::working_temporary_directory() /
            "monad_promote_repro_XXXXXX"};
        int const fd = ::mkstemp(reinterpret_cast<char *>(
            const_cast<char *>(filename.native().data())));
        MONAD_ASSERT(fd != -1);
        MONAD_ASSERT(-1 != ::ftruncate(fd, size_gb * 1024 * 1024 * 1024));
        ::close(fd);
        return filename;
    }
}

// Helpers for the page-encoded TrieRODb read regression test below.
namespace
{
    constexpr auto repro_val_a = bytes32_t{uint64_t{0xAA}};
    constexpr auto repro_val_b = bytes32_t{uint64_t{0xBB}};

    mpt::OnDiskDbConfig
    repro_cfg(std::filesystem::path const &dbfile, bool const append)
    {
        return mpt::OnDiskDbConfig{
            .append = append,
            .compaction = true,
            .sq_thread_cpu = std::nullopt,
            .dbname_paths = {dbfile},
            .fixed_history_length = 1000};
    }

    // Mirror the integration up to "page secondary populated by snapshot":
    // a slot primary with genesis + ADDR_A storage on two pages, activate a
    // page secondary, dump the slot primary, load the snapshot into the
    // secondary (slot->page re-encode). Leaves all Dbs closed.
    void seed_page_secondary_via_snapshot(
        std::filesystem::path const &dbfile,
        std::filesystem::path const &snapdir, uint64_t const version)
    {
        {
            mpt::Db db1{
                std::make_unique<OnDiskMachine>(), repro_cfg(dbfile, false)};
            TrieDb tdb1{db1};
            load_genesis_state(MonadTestnet{}.get_genesis_state(), tdb1);
            tdb1.set_block_and_prefix(0, {});
            BlockHeader const header{.number = version};
            auto deltas = make_deltas(
                std::nullopt,
                Account{.nonce = 1},
                {{slot_0, bytes32_t{}, repro_val_a},
                 {slot_far, bytes32_t{}, repro_val_b}});
            commit_block<MonadTraits<MONAD_ZERO>>(
                tdb1,
                nullptr,
                bytes32_t{version},
                header,
                deltas,
                make_empty_ancillaries());
            tdb1.finalize(version, bytes32_t{version});
        }
        {
            mpt::Db db1{
                std::make_unique<OnDiskMachine>(), repro_cfg(dbfile, true)};
            mpt::Db const db2 = db1.activate_secondary_timeline(
                std::make_unique<MonadOnDiskMachine>());
        }
        {
            std::array<char const *, 1> const paths{dbfile.c_str()};
            auto *const ctx =
                monad_db_snapshot_filesystem_write_user_context_create(
                    snapdir.c_str(), version);
            bool const ok = monad_db_dump_snapshot(
                paths.data(),
                paths.size(),
                std::numeric_limits<unsigned>::max(),
                version,
                monad_db_snapshot_write_filesystem,
                ctx,
                2048,
                1,
                0);
            MONAD_ASSERT(ok);
            monad_db_snapshot_filesystem_write_user_context_destroy(ctx);
        }
        {
            std::array<char const *, 1> const paths{dbfile.c_str()};
            monad_db_snapshot_load_filesystem(
                paths.data(),
                paths.size(),
                std::numeric_limits<unsigned>::max(),
                snapdir.c_str(),
                version,
                true);
        }
    }
}

TEST(MigrationFork, dual_write_state_root_handoff)
{
    ASSERT_EQ(compute_page_key(slot_0), compute_page_key(slot_1));
    ASSERT_NE(compute_page_key(slot_0), compute_page_key(slot_far));

    mpt::Db db1{std::make_unique<OnDiskMachine>(), mpt::OnDiskDbConfig{}};
    mpt::Db db2 =
        db1.activate_secondary_timeline(std::make_unique<MonadOnDiskMachine>());
    TrieDb tdb1{db1};
    TrieDb tdb2{db2};
    ASSERT_TRUE(tdb1.is_page_encoded() == false);
    ASSERT_TRUE(tdb2.is_page_encoded() == true);

    GenesisState const GENESIS_STATE = MonadTestnet{}.get_genesis_state();
    load_genesis_state(GENESIS_STATE, tdb1);
    load_genesis_state(GENESIS_STATE, tdb2);

    auto const make_block_id = [](uint64_t const n) { return bytes32_t{n}; };

    // Three pre fork blocks, then two post fork. Acct lifetime: created at
    // block 1, mutated each block. Slots are seeded then updated.
    Account acct{.nonce = 1};
    bytes32_t prev_id = {}; // genesis block_id

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
        tdb1.set_block_and_prefix(0, prev_id);
        tdb2.set_block_and_prefix(0, prev_id);
        auto deltas = make_deltas(
            std::nullopt,
            acct,
            {{slot_0, bytes32_t{}, bytes32_t{uint64_t{0xa1}}},
             {slot_1, bytes32_t{}, bytes32_t{uint64_t{0xb1}}}});
        drive_commit(tdb1, tdb2, Fork::Pre, 1, make_block_id(1), deltas);

        check_pre_fork_headers("block 1");

        EXPECT_EQ(
            tdb2.read_storage(ADDR_A, Incarnation{0, 0}, slot_0),
            bytes32_t{uint64_t{0xa1}});
        EXPECT_EQ(
            tdb2.read_storage(ADDR_A, Incarnation{0, 0}, slot_1),
            bytes32_t{uint64_t{0xb1}});

        prev_id = make_block_id(1);
    }

    // Block 2 (pre fork): touch slot_0 and seed slot_far (different page).
    {
        tdb1.set_block_and_prefix(1, prev_id);
        tdb2.set_block_and_prefix(1, prev_id);
        auto next = acct;
        next.nonce = 2;
        auto deltas = make_deltas(
            acct,
            next,
            {{slot_0, bytes32_t{uint64_t{0xa1}}, bytes32_t{uint64_t{0xa2}}},
             {slot_far, bytes32_t{}, bytes32_t{uint64_t{0xfa}}}});
        drive_commit(tdb1, tdb2, Fork::Pre, 2, make_block_id(2), deltas);
        acct = next;

        check_pre_fork_headers("block 2");
        prev_id = make_block_id(2);
    }

    // Block 3 (pre fork): account only churn (no storage writes).
    {
        tdb1.set_block_and_prefix(2, prev_id);
        tdb2.set_block_and_prefix(2, prev_id);
        auto next = acct;
        next.nonce = 3;
        auto deltas = make_deltas(acct, next, {});
        drive_commit(tdb1, tdb2, Fork::Pre, 3, make_block_id(3), deltas);
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
        tdb1.set_block_and_prefix(3, prev_id);
        tdb2.set_block_and_prefix(3, prev_id);
        auto next = acct;
        next.nonce = 4;
        auto deltas = make_deltas(
            acct,
            next,
            {{slot_1, bytes32_t{uint64_t{0xb1}}, bytes32_t{uint64_t{0xb4}}}});
        drive_commit(tdb1, tdb2, Fork::Post, 4, make_block_id(4), deltas);
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
        tdb1.set_block_and_prefix(4, prev_id);
        tdb2.set_block_and_prefix(4, prev_id);
        auto next = acct;
        next.nonce = 5;
        auto deltas = make_deltas(
            acct,
            next,
            {{slot_far, bytes32_t{uint64_t{0xfa}}, bytes32_t{uint64_t{0xf5}}}});
        drive_commit(tdb1, tdb2, Fork::Post, 5, make_block_id(5), deltas);
        acct = next;

        check_post_fork_headers("block 5");

        EXPECT_EQ(
            tdb2.read_storage(ADDR_A, Incarnation{0, 0}, slot_far),
            bytes32_t{uint64_t{0xf5}});
        EXPECT_EQ(
            tdb2.read_storage(ADDR_A, Incarnation{0, 0}, slot_1),
            bytes32_t{uint64_t{0xb4}});
        EXPECT_EQ(
            tdb2.read_storage(ADDR_A, Incarnation{0, 0}, slot_0),
            bytes32_t{uint64_t{0xa2}});
    }
}

// The page builder must honor the storage wipe on an incarnation change:
// when an account is destroyed and recreated (incarnation bump) and the new
// incarnation writes only a subset of its slots, the dead incarnation's
// untouched slots must NOT survive in the page-encoded Db2. PageCommitBuilder
// read-modify-merges pages via read_storage_page, which is incarnation-blind
// and runs before this block's wipe; without the empty-page-on-reincarnation
// guard it resurrects stale slots only on the page side, diverging the
// (post-fork canonical) page state root from the slot-encoded, EVM-correct
// Db1.
TEST(MigrationFork, reincarnation_does_not_resurrect_page_slots)
{
    mpt::Db db1{std::make_unique<OnDiskMachine>(), mpt::OnDiskDbConfig{}};
    mpt::Db db2 =
        db1.activate_secondary_timeline(std::make_unique<MonadOnDiskMachine>());
    TrieDb tdb1{db1};
    TrieDb tdb2{db2};
    ASSERT_FALSE(tdb1.is_page_encoded());
    ASSERT_TRUE(tdb2.is_page_encoded());

    GenesisState const GENESIS_STATE = MonadTestnet{}.get_genesis_state();
    load_genesis_state(GENESIS_STATE, tdb1);
    load_genesis_state(GENESIS_STATE, tdb2);

    auto const make_block_id = [](uint64_t const n) { return bytes32_t{n}; };
    bytes32_t prev_id = {};

    // Block 1: create the contract at incarnation {1,0}; seed slot_0 and
    // slot_1 (same page) plus slot_far (a different page).
    Account const inc1{.nonce = 1, .incarnation = Incarnation{1, 0}};
    {
        tdb1.set_block_and_prefix(0, prev_id);
        tdb2.set_block_and_prefix(0, prev_id);
        auto deltas = make_deltas(
            std::nullopt,
            inc1,
            {{slot_0, bytes32_t{}, bytes32_t{uint64_t{0xa1}}},
             {slot_1, bytes32_t{}, bytes32_t{uint64_t{0xb1}}},
             {slot_far, bytes32_t{}, bytes32_t{uint64_t{0xfa}}}});
        drive_commit(tdb1, tdb2, Fork::Post, 1, make_block_id(1), deltas);
        prev_id = make_block_id(1);
    }

    // Block 2: reincarnate ({1,0} -> {2,0}) and write ONLY slot_0. slot_1 and
    // slot_far belong to the dead incarnation; the new incarnation starts with
    // empty storage, so from its perspective slot_0 goes empty -> 0xc2.
    Account const inc2{.nonce = 1, .incarnation = Incarnation{2, 0}};
    {
        tdb1.set_block_and_prefix(1, prev_id);
        tdb2.set_block_and_prefix(1, prev_id);
        auto deltas = make_deltas(
            inc1, inc2, {{slot_0, bytes32_t{}, bytes32_t{uint64_t{0xc2}}}});
        drive_commit(tdb1, tdb2, Fork::Post, 2, make_block_id(2), deltas);
        prev_id = make_block_id(2);
    }

    // Db1 (slot) wipes exactly on the incarnation change, so it is the
    // EVM-correct oracle. Db2 (page) must agree slot-for-slot; on-disk reads
    // are incarnation-blind so the incarnation argument is immaterial here.
    auto const check = [&](bytes32_t const &slot,
                           bytes32_t const &want,
                           char const *const tag) {
        SCOPED_TRACE(tag);
        auto const v1 = tdb1.read_storage(ADDR_A, Incarnation{0, 0}, slot);
        auto const v2 = tdb2.read_storage(ADDR_A, Incarnation{0, 0}, slot);
        EXPECT_EQ(v1, want) << "slot-encoded Db1 (EVM oracle)";
        EXPECT_EQ(v2, want)
            << "page-encoded Db2 must match the oracle (no resurrection)";
    };
    check(
        slot_0,
        bytes32_t{uint64_t{0xc2}},
        "slot_0 rewritten by new incarnation");
    check(slot_1, bytes32_t{}, "slot_1 from dead incarnation must be wiped");
    check(
        slot_far, bytes32_t{}, "slot_far from dead incarnation must be wiped");
}

// TrieRODb must read page-encoded contract storage. Seed a page-encoded
// primary holding ADDR_A storage across two pages, open it read-only, and
// verify read_storage (per slot) and read_storage_page return the values.
TEST(MigrationFork, trie_rodb_reads_page_encoded_storage)
{
    namespace fs = std::filesystem;
    register_monad_state_machines();

    auto const dbfile = make_temp_db_file(4);
    fs::path const snapdir =
        fs::path{MONAD_ASYNC_NAMESPACE::working_temporary_directory()} /
        ("monad_trierodb_" + std::to_string(::getpid()));
    fs::create_directories(snapdir);

    constexpr uint64_t VERSION = 1;
    seed_page_secondary_via_snapshot(dbfile, snapdir, VERSION);
    {
        mpt::Db db1{repro_cfg(dbfile, true)};
        db1.promote_secondary_to_primary();
        db1.deactivate_secondary_timeline();
    }

    {
        mpt::ReadOnlyOnDiskDbConfig const ro_config{.dbname_paths = {dbfile}};
        mpt::RODb rodb{ro_config};
        TrieRODb trodb{rodb};
        EXPECT_TRUE(trodb.is_page_encoded());
        trodb.set_block_and_prefix(VERSION);
        EXPECT_EQ(
            trodb.read_storage(ADDR_A, Incarnation{0, 0}, slot_0), repro_val_a)
            << "TrieRODb failed to read page-encoded storage slot_0";
        EXPECT_EQ(
            trodb.read_storage(ADDR_A, Incarnation{0, 0}, slot_far),
            repro_val_b)
            << "TrieRODb failed to read page-encoded storage slot_far";
        auto const page = trodb.read_storage_page(
            ADDR_A, Incarnation{0, 0}, compute_page_key(slot_0));
        EXPECT_EQ(page[compute_slot_offset(slot_0)], repro_val_a)
            << "TrieRODb::read_storage_page returned the wrong page";
    }

    fs::remove(dbfile);
    fs::remove_all(snapdir);
}
