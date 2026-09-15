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

TrieDb::TrieDb(
    mpt::Db &db, bool const enable_multiblock_cache, bool const stamp_mode,
    DbCacheSizes const &sizes)
    : db_{db}
    , block_number_{db.get_latest_finalized_version()}
    , proposal_block_id_{bytes32_t{}}
    , prefix_{finalized_nibbles}
    , curr_root_{db.load_root_for_version(block_number_)}
    , cache_{enable_multiblock_cache ? std::make_unique<DbCache>(stamp_mode, sizes) : nullptr}
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

std::optional<storage_page_t> TrieDb::read_cache_ring_page(bytes32_t const &key)
{
    auto const res = db_.find(
        curr_root_,
        concat(
            prefix_,
            STATE_NIBBLE,
            NibblesView{keccak256(
                {STAMP_LOG_ADDRESS.bytes, sizeof(STAMP_LOG_ADDRESS.bytes)})},
            NibblesView{keccak256({key.bytes, sizeof(key.bytes)})}),
        block_number_);
    if (res.has_error()) {
        return std::nullopt;
    }
    auto const decoded = decode_storage_page_leaf(res.value().node->value());
    MONAD_ASSERT(decoded.has_value() && decoded.value().page_key == key);
    return decoded.value().page;
}

TrieDb::StampRebuildStats
TrieDb::rebuild_stamp_cache(fiber::PriorityPool *const pool)
{
    StampRebuildStats stats;
    if (!cache_) {
        return stats;
    }
    MONAD_ASSERT(prefix_ == finalized_nibbles);
    auto const log_account = read_account(STAMP_LOG_ADDRESS);
    MONAD_ASSERT_PRINTF(
        !log_account || log_account->nonce == 3,
        "unsupported cache log format; restore a pre-activation snapshot");
    CachePageReader const read = [this](bytes32_t const &key) {
        return read_cache_ring_page(key);
    };
    ProposalPostState post;
    post.cache_updated = true;
    post.cache_pricing = read_cache_pricing();
    visit_cache_ring(
        ACCOUNT_RING,
        read,
        [&](CacheRingRecord const &record, uint64_t stamp, bool deleted) {
            Address address;
            std::memcpy(address.bytes, record.key.bytes, 20);
            if (deleted) {
                post.account_stamps.erase(address);
            }
            else {
                post.account_stamps[address] = stamp;
            }
            ++stats.records;
        });
    visit_cache_ring(
        STORAGE_RING,
        read,
        [&](CacheRingRecord const &record, uint64_t stamp, bool deleted) {
            if (deleted) {
                post.storage_stamps.erase(record.key);
            }
            else {
                post.storage_stamps[record.key] = stamp;
            }
            ++stats.records;
        });
    stats.expected_accounts = post.account_stamps.size();
    stats.expected_pages = post.storage_stamps.size();
    ankerl::unordered_dense::segmented_set<Address> addresses;
    for (auto const &[key, stamp] : post.account_stamps) {
        addresses.insert(key);
    }
    for (auto const &[key, stamp] : post.storage_stamps) {
        Address address;
        Incarnation inc{0, 0};
        bytes32_t lookup;
        unpack_storage_key(key, address, inc, lookup);
        addresses.insert(address);
    }
    std::vector<Address> const account_keys(addresses.begin(), addresses.end());
    std::vector<std::optional<Account>> accounts(account_keys.size());
    parallel_for(pool, account_keys.size(), [&](size_t i) {
        accounts[i] = read_account(account_keys[i]);
    });
    for (size_t i = 0; i < account_keys.size(); ++i) {
        post.accounts.emplace(account_keys[i], accounts[i]);
    }
    for (auto const &entry : post.account_stamps) {
        if (post.accounts.at(entry.first)) {
            ++stats.accounts;
        }
        else {
            ++stats.absent_accounts;
        }
    }
    std::vector<StorageKey> page_keys;
    for (auto const &[key, stamp] : post.storage_stamps) {
        page_keys.push_back(key);
    }
    std::vector<storage_page_t> pages(page_keys.size());
    parallel_for(pool, page_keys.size(), [&](size_t i) {
        Address address;
        Incarnation inc{0, 0};
        bytes32_t lookup;
        unpack_storage_key(page_keys[i], address, inc, lookup);
        auto const &account = post.accounts.at(address);
        if (account && account->incarnation == inc) {
            pages[i] = load_storage_page(
                address, inc, lookup, CacheReadStatus::MissTruncated);
        }
    });
    for (size_t i = 0; i < page_keys.size(); ++i) {
        if (pages[i].is_empty()) {
            ++stats.absent_or_reincarnated_pages;
        }
        else {
            ++stats.pages;
            stats.slots += pages[i].size();
            post.storage.emplace(page_keys[i], std::move(pages[i]));
        }
    }
    cache_->rebuild_stamps(post);
    return stats;
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
    if (stamp == CACHE_STAMP_UNKNOWN) {
        CachePageReader const read = [this](bytes32_t const &key) {
            return read_cache_ring_page(key);
        };
        stamp = resolve_cache_stamp(
            ACCOUNT_RING,
            read,
            StorageKey{addr, Incarnation{0, 0}, bytes32_t{}});
    }
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
        // Stamp log leaves use page encoding even on slot-encoded databases.
        // They are read directly by bootstrap, outside ordinary storage reads.
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
    if (stamp == CACHE_STAMP_UNKNOWN) {
        CachePageReader const read = [this](bytes32_t const &key) {
            return read_cache_ring_page(key);
        };
        stamp = resolve_cache_stamp(
            STORAGE_RING, read, StorageKey{addr, incarnation, lookup_key});
    }
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
        bool const rebuild = cache_->on_finalize(block_number, block_id);
        cache_->set_block_and_prefix(block_number, bytes32_t{});
        if (rebuild) {
            rebuild_stamp_cache();
        }
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
