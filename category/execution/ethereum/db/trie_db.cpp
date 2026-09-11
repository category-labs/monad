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

#include <category/core/address.hpp>
#include <category/core/assert.h>
#include <category/core/byte_string.hpp>
#include <category/core/bytes.hpp>
#include <category/core/config.hpp>
#include <category/core/hex.hpp>
#include <category/core/keccak.hpp>
#include <category/core/likely.h>
#include <category/core/log.hpp>
#include <category/crypto/keccak.h>
#include <category/execution/ethereum/core/account.hpp>
#include <category/execution/ethereum/core/fmt/address_fmt.hpp> // NOLINT
#include <category/execution/ethereum/core/fmt/bytes_fmt.hpp> // NOLINT
#include <category/execution/ethereum/core/fmt/int_fmt.hpp> // NOLINT
#include <category/execution/ethereum/core/receipt.hpp>
#include <category/execution/ethereum/core/rlp/address_rlp.hpp>
#include <category/execution/ethereum/core/rlp/block_rlp.hpp>
#include <category/execution/ethereum/core/rlp/bytes_rlp.hpp>
#include <category/execution/ethereum/core/rlp/int_rlp.hpp>
#include <category/execution/ethereum/core/rlp/receipt_rlp.hpp>
#include <category/execution/ethereum/core/rlp/transaction_rlp.hpp>
#include <category/execution/ethereum/core/rlp/withdrawal_rlp.hpp>
#include <category/execution/ethereum/db/trie_db.hpp>
#include <category/execution/ethereum/db/util.hpp>
#include <category/execution/ethereum/rlp/encode2.hpp>
#include <category/execution/ethereum/state2/proposal_post_state.hpp>
#include <category/execution/ethereum/state2/state_deltas.hpp>
#include <category/execution/ethereum/trace/call_tracer.hpp>
#include <category/execution/ethereum/trace/rlp/call_frame_rlp.hpp>
#include <category/execution/ethereum/types/incarnation.hpp>
#include <category/execution/ethereum/validate_block.hpp>
#include <category/execution/monad/db/cache_pricing.hpp>
#include <category/execution/monad/db/page_commit_builder.hpp>
#include <category/execution/monad/db/stamp_log.hpp>
#include <category/execution/monad/db/storage_page.hpp>
#include <category/mpt/db.hpp>
#include <category/mpt/nibbles_view.hpp>
#include <category/mpt/nibbles_view_fmt.hpp> // NOLINT
#include <category/mpt/node.hpp>
#include <category/mpt/state_machine_kind.hpp>
#include <category/mpt/traverse.hpp>
#include <category/mpt/update.hpp>
#include <category/mpt/util.hpp>

#include <boost/fiber/future/promise.hpp>
#include <evmc/evmc.hpp>

#include <ankerl/unordered_dense.h>
#include <nlohmann/json.hpp>
#include <nlohmann/json_fwd.hpp>

#include <algorithm>
#include <atomic>
#include <chrono>
#include <cstdint>
#include <cstdlib>
#include <cstring>
#include <format>
#include <fstream>
#include <limits>
#include <memory>
#include <optional>
#include <span>
#include <string>
#include <utility>
#include <vector>

MONAD_NAMESPACE_BEGIN

using namespace monad::mpt;

TrieDb::TrieDb(
    mpt::Db &db, bool const enable_multiblock_cache, bool const stamp_mode)
    : db_{db}
    , block_number_{db.get_latest_finalized_version()}
    , proposal_block_id_{bytes32_t{}}
    , prefix_{finalized_nibbles}
    , curr_root_{db.load_root_for_version(block_number_)}
    , cache_{enable_multiblock_cache ? std::make_unique<DbCache>(stamp_mode) : nullptr}
    , page_encoded_{db_.state_machine_type() == mpt::state_machine_kind::monad}
{
}

TrieDb::~TrieDb() = default;

void TrieDb::reset_root(Node::SharedPtr root, uint64_t const block_number)
{
    curr_root_ = std::move(root);
    block_number_ = block_number;
}

Node::SharedPtr const &TrieDb::get_root() const
{
    return curr_root_;
}

namespace
{
    void unpack_storage_key(
        StorageKey const &key, Address &addr, Incarnation &inc,
        bytes32_t &lookup)
    {
        std::memcpy(addr.bytes, key.bytes, sizeof(addr.bytes));
        std::memcpy(&inc, key.bytes + sizeof(addr.bytes), sizeof(inc));
        std::memcpy(
            lookup.bytes,
            key.bytes + sizeof(addr.bytes) + sizeof(inc),
            sizeof(lookup.bytes));
    }

    // Run `fn(i)` for i in [0, n) across the pool in chunks, or inline.
    template <class Fn>
    void
    parallel_for(fiber::PriorityPool *const pool, size_t const n, Fn const &fn)
    {
        if (pool == nullptr || n < 1024) {
            for (size_t i = 0; i < n; ++i) {
                fn(i);
            }
            return;
        }
        size_t const chunks = std::min<size_t>(n / 256, pool->num_fibers());
        size_t const per_chunk = (n + chunks - 1) / chunks;
        std::vector<boost::fibers::promise<void>> done(chunks);
        for (size_t c = 0; c < chunks; ++c) {
            pool->submit(c, [&, c] {
                size_t const begin = c * per_chunk;
                size_t const end = std::min(n, begin + per_chunk);
                for (size_t i = begin; i < end; ++i) {
                    fn(i);
                }
                done[c].set_value();
            });
        }
        for (auto &d : done) {
            d.get_future().wait();
        }
    }
}

TrieDb::StampRebuildStats
TrieDb::rebuild_stamp_cache(fiber::PriorityPool *const pool)
{
    StampRebuildStats stats;
    if (!cache_) {
        return stats;
    }
    MONAD_ASSERT(prefix_ == finalized_nibbles);
    auto const log_prefix = concat(
        prefix_,
        STATE_NIBBLE,
        NibblesView{keccak256(
            {STAMP_LOG_ADDRESS.bytes, sizeof(STAMP_LOG_ADDRESS.bytes)})});
    auto const read_page =
        [&](uint64_t const slot, uint64_t const index, byte_string &record) {
            bytes32_t const page_key = stamp_log_page_key(slot, index);
            auto const res = db_.find(
                curr_root_,
                concat(
                    log_prefix,
                    NibblesView{
                        keccak256({page_key.bytes, sizeof(page_key.bytes)})}),
                block_number_);
            if (res.has_error()) {
                return false;
            }
            auto const decoded =
                decode_storage_page_leaf(res.value().node->value());
            MONAD_ASSERT(decoded.has_value());
            stamp_log_append_page(record, decoded.value().page);
            return true;
        };

    // ring slots never written read as empty and are skipped; a slot holds
    // the record of the most recent block congruent to it, so once the chain
    // is older than the window the ring is exactly the window
    std::vector<StampLogRecord> records;
    for (uint64_t slot = 0; slot < CACHE_WINDOW_BLOCKS; ++slot) {
        byte_string record;
        if (!read_page(slot, 0, record)) {
            continue;
        }
        auto const header = decode_stamp_log_header(record);
        MONAD_ASSERT(header.has_value());
        if (header->block == 0 || header->block > block_number_ ||
            header->block % CACHE_WINDOW_BLOCKS != slot ||
            header->block + CACHE_WINDOW_BLOCKS <= block_number_) {
            continue;
        }
        size_t const pages = stamp_log_pages(header->record_bytes());
        for (size_t i = 1; i < pages; ++i) {
            bool const ok = read_page(slot, i, record);
            MONAD_ASSERT_PRINTF(
                ok,
                "stamp log page %zu of block %lu missing",
                i,
                header->block);
        }
        auto rec = decode_stamp_log_record(record);
        MONAD_ASSERT(rec.has_value());
        records.push_back(std::move(rec.value()));
    }
    std::sort(records.begin(), records.end(), [](auto const &a, auto const &b) {
        return a.block < b.block;
    });
    if (char const *const dump = std::getenv("MONAD_MBC_DUMP")) {
        // debug aid: the ring as read, in the same format as the per-block
        // record dump of the runloop
        std::ofstream out(std::string{dump} + ".ring");
        for (auto const &rec : records) {
            for (auto const &a : rec.accounts) {
                out << rec.block << " A " << fmt::format("{}", a) << '\n';
            }
            for (auto const &k : rec.storage) {
                out << rec.block << " S 0x";
                for (auto const b : k.bytes) {
                    out << fmt::format("{:02x}", b);
                }
                out << '\n';
            }
        }
    }

    // Load every stamped item once, across the pool: accounts first (the
    // storage pass needs their incarnations), then storage pages. Items that
    // died or reincarnated since are not loaded and stay unstamped.
    ankerl::unordered_dense::segmented_set<Address> addresses;
    ankerl::unordered_dense::
        segmented_set<StorageKey, BytesHashCompare<StorageKey>>
            pages;
    for (auto const &rec : records) {
        for (auto const &a : rec.accounts) {
            addresses.insert(a);
        }
        for (auto const &k : rec.storage) {
            if (pages.insert(k).second) {
                Address addr;
                Incarnation inc{0, 0};
                bytes32_t lookup;
                unpack_storage_key(k, addr, inc, lookup);
                addresses.insert(addr);
            }
        }
    }
    std::vector<Address> const address_list(addresses.begin(), addresses.end());
    parallel_for(pool, address_list.size(), [&](size_t const i) {
        read_account(address_list[i]);
    });
    std::vector<StorageKey> const page_list(pages.begin(), pages.end());
    parallel_for(pool, page_list.size(), [&](size_t const i) {
        Address addr;
        Incarnation inc{0, 0};
        bytes32_t lookup;
        unpack_storage_key(page_list[i], addr, inc, lookup);
        auto const account = read_account(addr);
        if (!account.has_value() || account->incarnation != inc) {
            return;
        }
        storage_page_t page;
        auto const status =
            cache_->try_read_storage_page(addr, inc, lookup, page);
        if (status != CacheReadStatus::Hit) {
            load_storage_page(addr, inc, lookup, status);
        }
    });

    // Replay in block order: selections, then deaths, last writer wins. The
    // stamps and the live-list order end identical to a node that ran the
    // blocks itself.
    for (auto const &rec : records) {
        std::vector<Address> live_accounts;
        for (auto const &addr : rec.accounts) {
            std::optional<Account> account;
            if (cache_->try_read_account(addr, account) ==
                    CacheReadStatus::Hit &&
                account.has_value()) {
                live_accounts.push_back(addr);
            }
        }
        std::vector<StorageKey> live_pages;
        for (auto const &key : rec.storage) {
            Address addr;
            Incarnation inc{0, 0};
            bytes32_t lookup;
            unpack_storage_key(key, addr, inc, lookup);
            std::optional<Account> account;
            if (cache_->try_read_account(addr, account) !=
                    CacheReadStatus::Hit ||
                !account.has_value() || account->incarnation != inc) {
                continue;
            }
            storage_page_t page;
            if (cache_->try_read_storage_page(addr, inc, lookup, page) !=
                CacheReadStatus::Hit) {
                continue;
            }
            live_pages.push_back(key);
            stats.slots += page.size();
        }
        cache_->rebuild_stamps(
            live_accounts,
            live_pages,
            rec.dead_accounts,
            rec.dead_storage,
            rec.block);
        ++stats.records;
        stats.accounts += live_accounts.size();
        stats.pages += live_pages.size();
    }
    return stats;
}

bytes32_t
TrieDb::peek_storage_slot(Address const &addr, bytes32_t const &slot_key)
{
    MONAD_ASSERT(!page_encoded_);
    auto const res = db_.find(
        curr_root_,
        concat(
            prefix_,
            STATE_NIBBLE,
            NibblesView{keccak256({addr.bytes, sizeof(addr.bytes)})},
            NibblesView{keccak256({slot_key.bytes, sizeof(slot_key.bytes)})}),
        block_number_);
    if (res.has_error()) {
        return {};
    }
    return decode_storage_leaf_to_page(res.value().node->value(), false)[0];
}

uint32_t TrieDb::probe_page_occupancy(
    Address const &addr, Incarnation const inc, bytes32_t const &page_key)
{
    if (page_encoded_) {
        return static_cast<uint32_t>(
            read_storage_page(addr, inc, page_key).size());
    }
    // slot encoding: count the page's 128 concrete slots; cached per page
    // until one of them is written (TrieDb::commit invalidates)
    StorageKey const memo_key{addr, inc, page_key};
    if (auto const it = probe_memo_.find(memo_key); it != probe_memo_.end()) {
        return it->second;
    }
    uint32_t occupancy = 0;
    for (unsigned w = 0; w < storage_page_t::SLOTS; ++w) {
        bytes32_t const slot_key =
            compute_slot_key(page_key, static_cast<uint8_t>(w));
        bytes32_t value{};
        auto const status =
            cache_ ? cache_->try_read_storage(addr, inc, slot_key, 0, value)
                   : CacheReadStatus::MissTruncated;
        if (status != CacheReadStatus::Hit) {
            value = peek_storage_slot(addr, slot_key);
        }
        if (value != bytes32_t{}) {
            ++occupancy;
        }
    }
    probe_memo_[memo_key] = occupancy;
    return occupancy;
}

TrieDb::StampLogFootprint TrieDb::stamp_log_footprint()
{
    struct Count final : public TraverseMachine
    {
        StampLogFootprint fp;

        bool down(unsigned char const branch, Node const &node) override
        {
            if (branch != INVALID_BRANCH && node.has_value()) {
                ++fp.leaves;
                fp.value_bytes += node.value().size();
            }
            return true;
        }

        void up(unsigned char, Node const &) override {}

        std::unique_ptr<TraverseMachine> clone() const override
        {
            return std::make_unique<Count>(*this);
        }
    };

    auto const cursor = db_.find(
        curr_root_,
        concat(
            prefix_,
            STATE_NIBBLE,
            NibblesView{keccak256(
                {STAMP_LOG_ADDRESS.bytes, sizeof(STAMP_LOG_ADDRESS.bytes)})}),
        block_number_);
    if (!cursor.has_value() || !cursor.value().is_valid()) {
        return {};
    }
    Count count;
    if (db_.is_on_disk() && !db_.is_read_only()) {
        db_.traverse_blocking(cursor.value(), count, block_number_);
    }
    else {
        db_.traverse(cursor.value(), count, block_number_);
    }
    return count.fp;
}

std::optional<Account> TrieDb::read_account(Address const &addr)
{
    uint64_t stamp = 0;
    return read_account_stamped(addr, stamp);
}

std::optional<Account>
TrieDb::read_account_stamped(Address const &addr, uint64_t &stamp)
{
    stamp = 0;
    std::optional<Account> result;
    auto const status = cache_ ? cache_->try_read_account(addr, result, &stamp)
                               : CacheReadStatus::MissTruncated;
    if (status == CacheReadStatus::Hit) {
        return result;
    }
    auto const res = db_.find(
        curr_root_,
        concat(
            prefix_,
            STATE_NIBBLE,
            NibblesView{keccak256({addr.bytes, sizeof(addr.bytes)})}),
        block_number_);
    // result stays nullopt if absent at the finalized baseline.
    if (res.has_error()) {
        stats_account_no_value();
    }
    else {
        stats_account_value();
        auto encoded_account = res.value().node->value();
        result = decode_account_db_ignore_address(encoded_account).value();
    }
    if (cache_ && status == CacheReadStatus::MissResolved) {
        cache_->insert_account(addr, result);
    }
    return result;
}

bytes32_t TrieDb::read_storage(
    Address const &addr, Incarnation const incarnation, bytes32_t const &key)
{
    uint64_t stamp = 0;
    return read_storage_stamped(addr, incarnation, key, stamp);
}

bytes32_t TrieDb::read_storage_stamped(
    Address const &addr, Incarnation const incarnation, bytes32_t const &key,
    uint64_t &stamp)
{
    stamp = 0;
    if (MONAD_UNLIKELY(addr == STAMP_LOG_ADDRESS)) {
        // the stamp log is unreachable from the EVM; its leaves are page
        // encoded whatever the primary encoding, so never decode them here
        return {};
    }
    bytes32_t const lookup_key = storage_lookup_key(key);
    uint8_t const lookup_offset = page_encoded_ ? compute_slot_offset(key) : 0;
    bytes32_t result{};
    auto const status =
        cache_
            ? cache_->try_read_storage(
                  addr, incarnation, lookup_key, lookup_offset, result, &stamp)
            : CacheReadStatus::MissTruncated;
    if (status == CacheReadStatus::Hit) {
        return result;
    }
    return load_storage_page(
        addr, incarnation, lookup_key, status)[lookup_offset];
}

storage_page_t TrieDb::read_storage_page(
    Address const &addr, Incarnation const incarnation,
    bytes32_t const &page_key)
{
    if (!page_encoded_) {
        MONAD_ABORT("read_storage_page is only valid on a page-encoded TrieDb");
    }
    if (MONAD_UNLIKELY(addr == STAMP_LOG_ADDRESS)) {
        return {};
    }
    storage_page_t result;
    auto const status =
        cache_
            ? cache_->try_read_storage_page(addr, incarnation, page_key, result)
            : CacheReadStatus::MissTruncated;
    if (status == CacheReadStatus::Hit) {
        return result;
    }
    return load_storage_page(addr, incarnation, page_key, status);
}

storage_page_t TrieDb::load_storage_page(
    Address const &addr, Incarnation const incarnation,
    bytes32_t const &lookup_key, CacheReadStatus const status)
{
    auto const res = db_.find(
        curr_root_,
        concat(
            prefix_,
            STATE_NIBBLE,
            NibblesView{keccak256({addr.bytes, sizeof(addr.bytes)})},
            NibblesView{
                keccak256({lookup_key.bytes, sizeof(lookup_key.bytes)})}),
        block_number_);
    storage_page_t page;
    if (res.has_error()) {
        stats_storage_no_value();
    }
    else {
        stats_storage_value();
        page = decode_storage_leaf_to_page(
            res.value().node->value(), page_encoded_);
    }
    if (cache_ && status == CacheReadStatus::MissResolved) {
        cache_->insert_storage_page(addr, incarnation, lookup_key, page);
    }
    return page;
}

vm::SharedIntercode TrieDb::read_code(bytes32_t const &code_hash)
{
    // TODO read intercode object
    auto const res = db_.find(
        curr_root_,
        concat(
            prefix_,
            CODE_NIBBLE,
            NibblesView{to_byte_string_view(code_hash.bytes)}),
        block_number_);
    if (res.has_error()) {
        return vm::make_shared_intercode({});
    }
    return vm::make_shared_intercode(res.value().node->value());
}

void TrieDb::commit(
    bytes32_t const &block_id, CommitBuilder &builder,
    BlockHeader const &header, StateDeltas const & /*state_deltas*/,
    std::function<void(BlockHeader &)> const populate_header_fn)
{
    // The builder must be a PageCommitBuilder iff this db is page-encoded;
    // PageCommitBuilder is the only builder that produces page-keyed updates.
    MONAD_ASSERT_PRINTF(
        (dynamic_cast<PageCommitBuilder const *>(&builder) != nullptr) ==
            is_page_encoded(),
        "encoding mismatch at block %lu: TrieDb::is_page_encoded=%d but commit "
        "builder is of wrong type",
        header.number,
        is_page_encoded());

    auto const block_number = header.number;
    MONAD_ASSERT(block_number <= std::numeric_limits<int64_t>::max());

    auto const commit_begin = std::chrono::steady_clock::now();
    auto since = [&](std::chrono::steady_clock::time_point const t) {
        return std::chrono::duration_cast<std::chrono::microseconds>(
                   std::chrono::steady_clock::now() - t)
            .count();
    };
    MONAD_ASSERT(block_id != bytes32_t{});
    if (db_.is_on_disk() && block_id != proposal_block_id_) {
        auto const dest_prefix = proposal_prefix(block_id);
        if (db_.get_latest_version() != INVALID_BLOCK_NUM) {
            MONAD_ASSERT(block_number != block_number_);
            curr_root_ = db_.copy_trie(
                curr_root_,
                prefix_,
                db_.load_root_for_version(block_number),
                dest_prefix,
                block_number,
                false);
        }
        proposal_block_id_ = block_id;
        prefix_ = dest_prefix;
    }
    block_number_ = block_number;
    auto const t_copy = since(commit_begin);

    curr_root_ = db_.upsert(
        std::move(curr_root_),
        builder.build(prefix_),
        block_number_,
        true,
        true,
        false);
    auto const t_upsert = since(commit_begin);

    BlockHeader complete_header = header;
    MONAD_ASSERT(populate_header_fn);
    populate_header_fn(complete_header);
    auto const t_header = since(commit_begin);

    builder.add_block_header(complete_header);
    curr_root_ = db_.upsert(
        std::move(curr_root_), builder.build(prefix_), block_number_, false);
    auto const t_upsert2 = since(commit_begin);

    if (cache_) {
        ProposalPostState post = builder.take_proposal_post_state();
        // a write to any slot of a page invalidates its occupancy probe
        for (auto const &[sk, page] : post.storage) {
            Address addr;
            Incarnation inc{0, 0};
            bytes32_t lookup;
            std::memcpy(addr.bytes, sk.bytes, sizeof(addr.bytes));
            std::memcpy(&inc, sk.bytes + sizeof(addr.bytes), sizeof(inc));
            std::memcpy(
                lookup.bytes,
                sk.bytes + sizeof(addr.bytes) + sizeof(inc),
                sizeof(lookup.bytes));
            probe_memo_.erase(StorageKey{
                addr, inc, page_encoded_ ? lookup : compute_page_key(lookup)});
        }
        cache_->update_proposal_state(std::move(post), header.number, block_id);
    }
    auto const t_total = since(commit_begin);
    if (t_total > 30'000) {
        LOG_INFO(
            "__slow_commit,bl={},copy={}us,upsert={}us,header={}us,upsert2={}"
            "us,"
            "proposal={}us,total={}us",
            block_number,
            t_copy,
            t_upsert - t_copy,
            t_header - t_upsert,
            t_upsert2 - t_header,
            t_total - t_upsert2,
            t_total);
    }
}

void TrieDb::set_block_and_prefix(
    uint64_t const block_number, bytes32_t const &block_id)
{
    if (cache_) {
        cache_->set_block_and_prefix(block_number, block_id);
    }
    // set read state
    if (!db_.is_on_disk()) {
        MONAD_ASSERT(proposal_block_id_ == bytes32_t{});
        block_number_ = block_number;
        return;
    }
    prefix_ =
        block_id == bytes32_t{} ? finalized_nibbles : proposal_prefix(block_id);
    if (block_number_ != block_number) {
        curr_root_ = db_.load_root_for_version(block_number);
        block_number_ = block_number;
    }
    MONAD_ASSERT_PRINTF(
        db_.find(curr_root_, prefix_, block_number).has_value(),
        "Fail to find block_number %lu, block_id %s",
        block_number,
        fmt::format("{}", block_id).c_str());
    proposal_block_id_ = block_id;
}

// also changes internal state to the finalized state
void TrieDb::finalize(uint64_t const block_number, bytes32_t const &block_id)
{
    auto const latest_finalized = db_.get_latest_finalized_version();
    MONAD_ASSERT_PRINTF(
        latest_finalized == INVALID_BLOCK_NUM ||
            block_number == latest_finalized ||
            block_number == latest_finalized + 1,
        "Finalized version must advance by at most one block. block to "
        "finalize %lu must equal latest_finalized %lu or latest_finalized + 1",
        block_number,
        latest_finalized);

    MONAD_ASSERT(block_id != bytes32_t{});
    if (db_.is_on_disk()) {
        auto const src_prefix = proposal_prefix(block_id);
        auto root = (block_number_ == block_number)
                        ? curr_root_
                        : db_.load_root_for_version(block_number);
        MONAD_ASSERT(db_.find(root, src_prefix, block_number).has_value());
        curr_root_ = db_.copy_trie(
            root, src_prefix, root, finalized_nibbles, block_number, true);
        prefix_ = finalized_nibbles;
    }
    block_number_ = block_number;
    db_.update_finalized_version(block_number);
    if (cache_) {
        cache_->on_finalize(block_number, block_id);
    }
}

void TrieDb::update_verified_block(uint64_t const block_number)
{
    auto const latest_verified = db_.get_latest_verified_version();
    MONAD_ASSERT_PRINTF(
        latest_verified == INVALID_BLOCK_NUM || block_number >= latest_verified,
        "block_number %lu must be gte last_verified %lu",
        block_number,
        latest_verified);
    db_.update_verified_version(block_number);
}

void TrieDb::update_voted_metadata(
    uint64_t const block_number, bytes32_t const &block_id)
{
    db_.update_voted_metadata(block_number, block_id);
}

void TrieDb::update_proposed_metadata(
    uint64_t const block_number, bytes32_t const &block_id)
{
    db_.update_proposed_metadata(block_number, block_id);
}

bytes32_t TrieDb::state_root()
{
    return merkle_root(state_nibbles);
}

bytes32_t TrieDb::receipts_root()
{
    return merkle_root(receipt_nibbles);
}

bytes32_t TrieDb::transactions_root()
{
    return merkle_root(transaction_nibbles);
}

std::optional<bytes32_t> TrieDb::withdrawals_root()
{
    auto const res =
        db_.find(curr_root_, concat(prefix_, WITHDRAWAL_NIBBLE), block_number_);
    if (res.has_error()) {
        return std::nullopt;
    }
    auto const data = res.value().node->data();
    if (data.empty()) {
        return NULL_ROOT;
    }
    MONAD_ASSERT(data.size() == sizeof(bytes32_t));
    return to_bytes(data);
}

bytes32_t TrieDb::merkle_root(Nibbles const &nibbles)
{
    auto const res = db_.find(
        curr_root_, concat(prefix_, NibblesView{nibbles}), block_number_);
    if (!res.has_value() || res.value().node->data().empty()) {
        return NULL_ROOT;
    }
    auto const data = res.value().node->data();
    MONAD_ASSERT(data.size() == sizeof(bytes32_t));
    return to_bytes(data);
}

BlockHeader TrieDb::read_eth_header()
{
    auto const query_res = db_.find(
        curr_root_, concat(prefix_, BLOCKHEADER_NIBBLE), block_number_);
    MONAD_ASSERT(!query_res.has_error());
    auto encoded_header_db = query_res.value().node->value();
    auto decode_res = rlp::decode_block_header(encoded_header_db);
    MONAD_ASSERT_PRINTF(
        decode_res.has_value(),
        "FATAL: Could not decode eth header : %s",
        decode_res.error().message().c_str());
    return std::move(decode_res.value());
}

std::string TrieDb::print_stats()
{
    std::string ret;
    ret += std::format(
        ",ae={:4},ane={:4},sz={:4},snz={:4}",
        n_account_no_value_.load(std::memory_order_acquire),
        n_account_value_.load(std::memory_order_acquire),
        n_storage_no_value_.load(std::memory_order_acquire),
        n_storage_value_.load(std::memory_order_acquire));
    n_account_no_value_.store(0, std::memory_order_release);
    n_account_value_.store(0, std::memory_order_release);
    n_storage_no_value_.store(0, std::memory_order_release);
    n_storage_value_.store(0, std::memory_order_release);
    if (cache_) {
        ret += ",ac=" + cache_->accounts_stats() +
               ",sc=" + cache_->storage_stats();
    }
    return ret;
}

nlohmann::json TrieDb::to_json(size_t const concurrency_limit)
{
    struct Traverse : public TraverseMachine
    {
        TrieDb &db;
        nlohmann::json &json;
        Nibbles path{};

        explicit Traverse(TrieDb &db, nlohmann::json &json)
            : db(db)
            , json(json)
        {
        }

        virtual bool down(unsigned char const branch, Node const &node) override
        {
            if (branch == INVALID_BRANCH) {
                MONAD_ASSERT(node.path_nibble_view().nibble_size() == 0);
                return true;
            }
            path = concat(NibblesView{path}, branch, node.path_nibble_view());

            if (path.nibble_size() == (KECCAK256_SIZE * 2)) {
                handle_account(node);
            }
            else if (
                path.nibble_size() == ((KECCAK256_SIZE + KECCAK256_SIZE) * 2)) {
                handle_storage(node);
            }
            return true;
        }

        virtual void up(unsigned char const branch, Node const &node) override
        {
            auto const path_view = NibblesView{path};
            auto const rem_size = [&] {
                if (branch == INVALID_BRANCH) {
                    MONAD_ASSERT(path_view.nibble_size() == 0);
                    return 0;
                }
                int const rem_size = path_view.nibble_size() - 1 -
                                     node.path_nibble_view().nibble_size();
                MONAD_ASSERT(rem_size >= 0);
                MONAD_ASSERT(
                    path_view.substr(static_cast<unsigned>(rem_size)) ==
                    concat(branch, node.path_nibble_view()));
                return rem_size;
            }();
            path = path_view.substr(0, static_cast<unsigned>(rem_size));
        }

        void handle_account(Node const &node)
        {
            MONAD_ASSERT(node.has_value());

            auto encoded_account = node.value();

            auto acct = decode_account_db(encoded_account);

            auto const key = fmt::format("{}", NibblesView{path});

            json[key]["address"] = fmt::format("{}", acct.value().first);
            json[key]["balance"] =
                fmt::format("{}", acct.value().second.balance);
            json[key]["nonce"] =
                fmt::format("0x{:x}", acct.value().second.nonce);

            auto const icode = db.read_code(acct.value().second.code_hash);
            MONAD_ASSERT(icode);
            json[key]["code"] = "0x" + to_hex({icode->code(), icode->size()});

            if (!json[key].contains("storage")) {
                json[key]["storage"] = nlohmann::json::object();
            }
        }

        void handle_storage(Node const &node)
        {
            MONAD_ASSERT(node.has_value());

            auto const acct_key = fmt::format(
                "{}", NibblesView{path}.substr(0, KECCAK256_SIZE * 2));

            if (db.is_page_encoded()) {
                // Page-encoded leaf: fan out one JSON entry per populated slot,
                // keyed by keccak256(slot_key) so the output matches a slot
                // dump.
                auto const decoded = decode_storage_page_leaf(node.value());
                MONAD_ASSERT(decoded.has_value());
                for (auto const [slot_key, slot_value] :
                     decoded.value().slots()) {
                    auto const hashed_slot_key = to_bytes(
                        keccak256({slot_key.bytes, sizeof(slot_key.bytes)}));
                    auto const key = fmt::format("{}", hashed_slot_key);
                    auto storage_data_json = nlohmann::json::object();
                    storage_data_json["slot"] = fmt::format(
                        "0x{:02x}",
                        fmt::join(
                            std::as_bytes(std::span(slot_key.bytes)), ""));
                    storage_data_json["value"] = fmt::format(
                        "0x{:02x}",
                        fmt::join(
                            std::as_bytes(std::span(slot_value.bytes)), ""));
                    json[acct_key]["storage"][key] = storage_data_json;
                }
            }
            else {
                // Slot-encoded leaf: trie path under the account is
                // keccak256(slot_key); the leaf carries (slot_key,
                // slot_value).
                auto encoded_storage = node.value();
                auto const raw_res = decode_storage_db_raw(encoded_storage);
                MONAD_ASSERT(raw_res.has_value());
                bytes32_t const slot_key = to_bytes(raw_res.value().first);
                bytes32_t const slot_value = to_bytes(raw_res.value().second);
                auto const key = fmt::format(
                    "{}",
                    NibblesView{path}.substr(
                        KECCAK256_SIZE * 2, KECCAK256_SIZE * 2));

                auto storage_data_json = nlohmann::json::object();
                storage_data_json["slot"] = fmt::format(
                    "0x{:02x}",
                    fmt::join(std::as_bytes(std::span(slot_key.bytes)), ""));
                storage_data_json["value"] = fmt::format(
                    "0x{:02x}",
                    fmt::join(std::as_bytes(std::span(slot_value.bytes)), ""));
                json[acct_key]["storage"][key] = storage_data_json;
            }
        }

        virtual std::unique_ptr<TraverseMachine> clone() const override
        {
            return std::make_unique<Traverse>(*this);
        }
    };

    auto json = nlohmann::json::object();
    Traverse traverse(*this, json);

    auto res_cursor =
        db_.find(curr_root_, concat(prefix_, STATE_NIBBLE), block_number_);
    MONAD_ASSERT(res_cursor.has_value());
    MONAD_ASSERT(res_cursor.value().is_valid());
    // RWOndisk Db prevents any parallel traversal that does blocking i/o
    // from running on the triedb thread, which include to_json. Thus, we can
    // only use blocking traversal for RWOnDisk Db, but can still do parallel
    // traverse in other cases.
    if (db_.is_on_disk() && !db_.is_read_only()) {
        MONAD_ASSERT(
            db_.traverse_blocking(res_cursor.value(), traverse, block_number_));
    }
    else {
        MONAD_ASSERT(db_.traverse(
            res_cursor.value(), traverse, block_number_, concurrency_limit));
    }

    return json;
}

uint64_t TrieDb::get_block_number() const
{
    return block_number_;
}

uint64_t TrieDb::get_history_length() const
{
    return db_.get_history_length();
}

MONAD_NAMESPACE_END
