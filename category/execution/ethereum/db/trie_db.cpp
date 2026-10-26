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
#include <category/core/log.hpp>
#include <category/crypto/keccak.h>
#include <category/execution/ethereum/core/account.hpp>
#include <category/execution/ethereum/core/fmt/address_fmt.hpp>
#include <category/execution/ethereum/core/fmt/bytes_fmt.hpp>
#include <category/execution/ethereum/core/fmt/int_fmt.hpp>
#include <category/execution/ethereum/core/receipt.hpp>
#include <category/execution/ethereum/core/rlp/address_rlp.hpp>
#include <category/execution/ethereum/core/rlp/block_rlp.hpp>
#include <category/execution/ethereum/core/rlp/bytes_rlp.hpp>
#include <category/execution/ethereum/core/rlp/int_rlp.hpp>
#include <category/execution/ethereum/core/rlp/receipt_rlp.hpp>
#include <category/execution/ethereum/core/rlp/transaction_rlp.hpp>
#include <category/execution/ethereum/core/rlp/withdrawal_rlp.hpp>
#include <category/execution/ethereum/db/partitioned_commit_builder.hpp>
#include <category/execution/ethereum/db/partitioned_layout.hpp>
#include <category/execution/ethereum/db/storage_stats.hpp>
#include <category/execution/ethereum/db/trie_db.hpp>
#include <category/execution/ethereum/db/util.hpp>
#include <category/execution/ethereum/rlp/encode2.hpp>
#include <category/execution/ethereum/state2/proposal_post_state.hpp>
#include <category/execution/ethereum/state2/state_deltas.hpp>
#include <category/execution/ethereum/trace/call_tracer.hpp>
#include <category/execution/ethereum/trace/rlp/call_frame_rlp.hpp>
#include <category/execution/ethereum/types/incarnation.hpp>
#include <category/execution/ethereum/validate_block.hpp>
#include <category/execution/monad/db/page_commit_builder.hpp>
#include <category/execution/monad/db/storage_page.hpp>
#include <category/mpt/db.hpp>
#include <category/mpt/nibbles_view.hpp>
#include <category/mpt/nibbles_view_fmt.hpp>
#include <category/mpt/node.hpp>
#include <category/mpt/state_machine_kind.hpp>
#include <category/mpt/traverse.hpp>
#include <category/mpt/update.hpp>
#include <category/mpt/util.hpp>

#include <evmc/evmc.hpp>

#include <nlohmann/json.hpp>
#include <nlohmann/json_fwd.hpp>

#include <algorithm>
#include <atomic>
#include <cstdint>
#include <cstdlib>
#include <cstring>
#include <format>
#include <limits>
#include <memory>
#include <optional>
#include <span>
#include <string>
#include <utility>
#include <vector>

MONAD_NAMESPACE_BEGIN

using namespace monad::mpt;

TrieDb::TrieDb(mpt::Db &db, bool const enable_multiblock_cache)
    : db_{db}
    , block_number_{db.get_latest_finalized_version()}
    , proposal_block_id_{bytes32_t{}}
    , prefix_{finalized_nibbles}
    , curr_root_{db.load_root_for_version(block_number_)}
    , cache_{enable_multiblock_cache ? std::make_unique<DbCache>() : nullptr}
    , page_encoded_{db_.state_machine_type() == mpt::state_machine_kind::monad}
    , partitioned_{
          db_.state_machine_type() == mpt::state_machine_kind::partitioned}
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

std::optional<Account> TrieDb::read_account(Address const &addr)
{
    std::optional<Account> result;
    auto const status = cache_ ? cache_->try_read_account(addr, result)
                               : CacheReadStatus::MissTruncated;
    if (status == CacheReadStatus::Hit) {
        return result;
    }
    if (partitioned_) {
        result = read_account_partitioned(addr, status);
    }
    else {
        auto const res = db_.find(
            curr_root_,
            concat(
                prefix_,
                STATE_NIBBLE,
                NibblesView{state_key_hash({addr.bytes, sizeof(addr.bytes)})}),
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
    }
    if (cache_ && status == CacheReadStatus::MissResolved) {
        cache_->insert_account(addr, result);
    }
    return result;
}

::monad::Db::AccountRead TrieDb::read_account_and_header(Address const &addr)
{
    using namespace partitioned;
    if (!partitioned_) {
        return {.account = read_account(addr), .header_storage = {}};
    }
    std::optional<Account> account;
    auto const status = cache_ ? cache_->try_read_account(addr, account)
                               : CacheReadStatus::MissTruncated;
    if (status == CacheReadStatus::Hit) {
        if (!account.has_value()) {
            return {.account = std::nullopt, .header_storage = {}};
        }
        storage_page_t page;
        auto const page_status = cache_->try_read_storage_page(
            addr, account->incarnation, HEADER_PAGE_KEY, page);
        if (page_status != CacheReadStatus::Hit) {
            page = load_storage_partitioned(
                addr, account->incarnation, HEADER_PAGE_KEY, page_status);
        }
        return {.account = account, .header_storage = std::move(page)};
    }
    auto leaf = load_account_leaf_partitioned(addr);
    if (!leaf.has_value()) {
        stats_account_no_value();
    }
    else {
        stats_account_value();
        account = leaf->account;
    }
    if (cache_ && status == CacheReadStatus::MissResolved) {
        cache_->insert_account(addr, account);
        if (leaf.has_value()) {
            cache_->insert_storage_page(
                addr, leaf->account.incarnation, HEADER_PAGE_KEY, leaf->header);
        }
    }
    if (!leaf.has_value()) {
        return {.account = std::nullopt, .header_storage = {}};
    }
    return {.account = account, .header_storage = std::move(leaf->header)};
}

std::optional<partitioned::AccountLeaf>
TrieDb::load_account_leaf_partitioned(Address const &addr)
{
    using namespace partitioned;
    auto const res = db_.find(
        curr_root_,
        concat(prefix_, STATE_NIBBLE, NibblesView{header_stem_nibbles(addr)}),
        block_number_);
    if (res.has_error()) {
        return std::nullopt;
    }
    auto leaf = decode_account_leaf(res.value().node->value());
    MONAD_ASSERT_PRINTF(leaf.has_value(), "malformed account leaf");
    return leaf;
}

// The account is the leaf at its header stem key; it exists iff the leaf
// does. The leaf also carries the header slot page, cached alongside so the
// slots cost no further read.
std::optional<Account> TrieDb::read_account_partitioned(
    Address const &addr, CacheReadStatus const status)
{
    auto leaf = load_account_leaf_partitioned(addr);
    if (!leaf.has_value()) {
        stats_account_no_value();
        return std::nullopt;
    }
    stats_account_value();
    if (cache_ && status == CacheReadStatus::MissResolved) {
        cache_->insert_storage_page(
            addr,
            leaf->account.incarnation,
            partitioned::HEADER_PAGE_KEY,
            leaf->header);
    }
    return leaf->account;
}

bool TrieDb::storage_bucket_exists(Address const &addr)
{
    MONAD_ASSERT(partitioned_);
    return db_
        .find(
            curr_root_,
            concat(
                prefix_,
                STATE_NIBBLE,
                NibblesView{partitioned::storage_stem_nibbles(addr)}),
            block_number_)
        .has_value();
}

bytes32_t TrieDb::read_storage(
    Address const &addr, Incarnation const incarnation, bytes32_t const &key)
{
    // Lookup key and in-page offset: the page key and slot offset for the
    // page and partitioned layouts (page 0 being the partitioned header), the
    // slot itself at offset 0 for the slot layout
    bool const paged = page_encoded_ || partitioned_;
    bytes32_t const lookup_key = paged ? compute_page_key(key) : key;
    uint8_t const lookup_offset = paged ? compute_slot_offset(key) : 0;
    bytes32_t result{};
    auto const status =
        cache_ ? cache_->try_read_storage(
                     addr, incarnation, lookup_key, lookup_offset, result)
               : CacheReadStatus::MissTruncated;
    if (status == CacheReadStatus::Hit) {
        return result;
    }
    if (partitioned_) {
        return load_storage_partitioned(
            addr, incarnation, lookup_key, status)[lookup_offset];
    }
    return load_storage_page(
        addr, incarnation, lookup_key, status)[lookup_offset];
}

storage_page_t TrieDb::load_storage_partitioned(
    Address const &addr, Incarnation const incarnation,
    bytes32_t const &lookup_key, CacheReadStatus const status)
{
    using namespace partitioned;
    storage_page_t page;
    if (lookup_key == HEADER_PAGE_KEY) {
        auto leaf = load_account_leaf_partitioned(addr);
        if (!leaf.has_value()) {
            stats_storage_no_value();
        }
        else {
            stats_storage_value();
            page = std::move(leaf->header);
        }
    }
    else {
        auto const res = db_.find(
            curr_root_,
            concat(
                prefix_,
                STATE_NIBBLE,
                NibblesView{storage_page_key_nibbles(addr, lookup_key)}),
            block_number_);
        if (res.has_error()) {
            stats_storage_no_value();
        }
        else {
            stats_storage_value();
            auto decoded = decode_storage_page(res.value().node->value());
            MONAD_ASSERT(decoded.has_value());
            page = std::move(decoded).value();
        }
    }
    if (cache_ && status == CacheReadStatus::MissResolved) {
        cache_->insert_storage_page(addr, incarnation, lookup_key, page);
    }
    return page;
}

storage_page_t TrieDb::read_storage_page(
    Address const &addr, Incarnation const incarnation,
    bytes32_t const &page_key)
{
    if (!page_encoded_ && !partitioned_) {
        MONAD_ABORT("read_storage_page is only valid on a page-encoded TrieDb");
    }
    storage_page_t result;
    auto const status =
        cache_
            ? cache_->try_read_storage_page(addr, incarnation, page_key, result)
            : CacheReadStatus::MissTruncated;
    if (status == CacheReadStatus::Hit) {
        return result;
    }
    if (partitioned_) {
        return load_storage_partitioned(addr, incarnation, page_key, status);
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
            NibblesView{state_key_hash({addr.bytes, sizeof(addr.bytes)})},
            NibblesView{
                state_key_hash({lookup_key.bytes, sizeof(lookup_key.bytes)})}),
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
    MONAD_ASSERT_PRINTF(
        (dynamic_cast<PartitionedCommitBuilder const *>(&builder) != nullptr) ==
            is_partitioned(),
        "layout mismatch at block %lu: TrieDb::is_partitioned=%d but commit "
        "builder is of wrong type",
        header.number,
        is_partitioned());

    auto const block_number = header.number;
    MONAD_ASSERT(block_number <= std::numeric_limits<int64_t>::max());

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

    curr_root_ = db_.upsert(
        std::move(curr_root_),
        builder.build(prefix_),
        block_number_,
        true,
        true,
        false);

    BlockHeader complete_header = header;
    MONAD_ASSERT(populate_header_fn);
    populate_header_fn(complete_header);

    builder.add_block_header(complete_header);
    curr_root_ = db_.upsert(
        std::move(curr_root_), builder.build(prefix_), block_number_, false);

    if (cache_) {
        cache_->update_proposal_state(
            builder.take_proposal_post_state(), header.number, block_id);
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

// Finalizes the trie for `block_id` by copying its proposal trie into the
// finalized prefix on disk. Does not modify the internal state used by
// subsequent reads, such as `prefix_` or `block_number_`.
//
// The in-memory trie represented by `curr_root_` is only updated when
// finalizing the current block, in which case `curr_root_` is updated to keep
// the cache consistent with disk.
//
// For non-current block finalization, the in-memory trie is intentionally left
// unchanged so that subsequent in-order `set_block_and_prefix` calls can reuse
// cached top-level nodes instead of cold-loading from disk.
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
        bool const is_current_block = block_number_ == block_number;
        auto root = is_current_block ? curr_root_
                                     : db_.load_root_for_version(block_number);
        MONAD_ASSERT(db_.find(root, src_prefix, block_number).has_value());
        root = db_.copy_trie(
            root, src_prefix, root, finalized_nibbles, block_number, true);
        if (is_current_block) {
            curr_root_ = std::move(root);
        }
    }
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
    // Storage reads reaching BlockState and slots written at commit, with
    // the share in the first page (slot < 128): see storage_stats.hpp
    ret += std::format(
        ",sread={:5},sreadp={:5},swrite={:5},swritep={:5}",
        storage_stats::reads.exchange(0, std::memory_order_relaxed),
        storage_stats::reads_first_page.exchange(0, std::memory_order_relaxed),
        storage_stats::writes.exchange(0, std::memory_order_relaxed),
        storage_stats::writes_first_page.exchange(
            0, std::memory_order_relaxed));
    // Per-interval AsyncIO counters of the db's io (on-disk dbs only): reads
    // and writes submitted, KiB read and written, reads retried on EAGAIN,
    // and the peak in-flight depth since start. Read across threads as a
    // statistic, see AsyncIO::records().
    if (auto const *const io = db_.io(); io != nullptr) {
        async::IORecord const rec = io->records();
        ret += std::format(
            ",ior={:6},iorkb={:7},iow={:5},iowkb={:7},iorr={:3},iomax={:3}/"
            "{:3}",
            rec.nreads - last_io_records_.nreads,
            (rec.bytes_read - last_io_records_.bytes_read) / 1024,
            rec.nwrites - last_io_records_.nwrites,
            (rec.bytes_written - last_io_records_.bytes_written) / 1024,
            rec.reads_retried - last_io_records_.reads_retried,
            rec.max_inflight_rd,
            rec.max_inflight_wr);
        last_io_records_ = rec;
    }
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
                    auto const hashed_slot_key = to_bytes(state_key_hash(
                        {slot_key.bytes, sizeof(slot_key.bytes)}));
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

    MONAD_ASSERT_PRINTF(
        !partitioned_, "to_json is not implemented for the partitioned layout");
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
