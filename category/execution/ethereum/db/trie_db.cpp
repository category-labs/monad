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

#include <category/core/assert.h>
#include <category/core/blake3.hpp>
#include <category/core/byte_string.hpp>
#include <category/core/bytes.hpp>
#include <category/core/config.hpp>
#include <category/core/keccak.h>
#include <category/core/keccak.hpp>
#include <category/execution/ethereum/core/account.hpp>
#include <category/execution/ethereum/core/address.hpp>
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
#include <category/execution/ethereum/state2/state_deltas.hpp>
#include <category/execution/ethereum/trace/call_tracer.hpp>
#include <category/execution/ethereum/trace/rlp/call_frame_rlp.hpp>
#include <category/execution/ethereum/types/incarnation.hpp>
#include <category/execution/ethereum/validate_block.hpp>
#include <category/mpt/db.hpp>
#include <category/mpt/nibbles_view.hpp>
#include <category/mpt/nibbles_view_fmt.hpp> // NOLINT
#include <category/mpt/node.hpp>
#include <category/mpt/traverse.hpp>
#include <category/mpt/update.hpp>
#include <category/mpt/util.hpp>

#include <evmc/evmc.hpp>
#include <evmc/hex.hpp>

#include <nlohmann/json.hpp>
#include <nlohmann/json_fwd.hpp>

#include <quill/bundled/fmt/core.h>
#include <quill/bundled/fmt/format.h>

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

TrieDb::TrieDb(mpt::Db &db)
    : db_{db}
    , block_number_{db.get_latest_finalized_version()}
    , proposal_block_id_{bytes32_t{}}
    , prefix_{finalized_nibbles}
    , curr_root_{db.load_root_for_version(block_number_)}
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
    auto const res = db_.find(
        curr_root_,
        concat(
            prefix_,
            STATE_NIBBLE,
            NibblesView{keccak256({addr.bytes, sizeof(addr.bytes)})}),
        block_number_);
    if (res.has_error()) {
        stats_account_no_value();
        return std::nullopt;
    }
    stats_account_value();

    auto encoded_account = res.value().node->value();
    auto const acct = decode_account_db_ignore_address(encoded_account);
    MONAD_DEBUG_ASSERT(!acct.has_error());
    return acct.value();
}

bytes32_t
TrieDb::read_storage(Address const &addr, Incarnation, bytes32_t const &key)
{
    auto const res = db_.find(
        curr_root_,
        concat(
            prefix_,
            STATE_NIBBLE,
            NibblesView{keccak256({addr.bytes, sizeof(addr.bytes)})},
            STORAGE_PREFIX_NIBBLE,
            NibblesView{keccak256({key.bytes, sizeof(key.bytes)})}),
        block_number_);
    if (res.has_error()) {
        stats_storage_no_value();
        return {};
    }
    stats_storage_value();
    auto encoded_storage = res.value().node->value();
    auto const storage = decode_storage_db_ignore_slot(encoded_storage);
    MONAD_ASSERT(!storage.has_error());
    return to_bytes(storage.value());
};

bytes4k_t TrieDb::read_block_storage(
    Address const &addr, Incarnation, bytes32_t const &key)
{
    auto const res = db_.find(
        curr_root_,
        concat(
            prefix_,
            STATE_NIBBLE,
            NibblesView{keccak256({addr.bytes, sizeof(addr.bytes)})},
            BLOCK_STORAGE_PREFIX_NIBBLE,
            NibblesView{blake3({key.bytes, sizeof(key.bytes)})}),
        block_number_);
    if (res.has_error()) {
        stats_storage_no_value();
        return bytes4k_t{};
    }
    stats_storage_value();
    auto encoded_storage = res.value().node->value();
    auto const storage = decode_storage_db_ignore_slot(encoded_storage);
    MONAD_ASSERT(!storage.has_error());
    return to_page(storage.value());
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
    StateDeltas const &state_deltas, Code const &code,
    bytes32_t const &block_id, BlockHeader const &header,
    std::vector<Receipt> const &receipts,
    std::vector<std::vector<CallFrame>> const &call_frames,
    std::vector<Address> const &senders,
    std::vector<Transaction> const &transactions,
    std::vector<BlockHeader> const &ommers,
    std::optional<std::vector<Withdrawal>> const &withdrawals)
{
    MONAD_ASSERT(header.number <= std::numeric_limits<int64_t>::max());

    MONAD_ASSERT(block_id != bytes32_t{});
    if (db_.is_on_disk() && block_id != proposal_block_id_) {
        auto const dest_prefix = proposal_prefix(block_id);
        if (db_.get_latest_version() != INVALID_BLOCK_NUM) {
            MONAD_ASSERT(header.number != block_number_);
            curr_root_ = db_.copy_trie(
                curr_root_,
                prefix_,
                db_.load_root_for_version(header.number),
                dest_prefix,
                header.number,
                false);
        }
        proposal_block_id_ = block_id;
        prefix_ = dest_prefix;
    }
    block_number_ = header.number;

    CommitBuilder builder(block_number_);
    builder.add_state_deltas(state_deltas)
        .add_code(code)
        .add_receipts(receipts)
        .add_transactions(transactions, senders)
        .add_call_frames(call_frames)
        .add_ommers(ommers);
    if (withdrawals.has_value()) {
        builder.add_withdrawals(withdrawals.value());
    }

    curr_root_ = db_.upsert(
        std::move(curr_root_),
        builder.build(prefix_),
        block_number_,
        true,
        true,
        false);

    BlockHeader complete_header = header;
    if (MONAD_LIKELY(header.receipts_root == NULL_ROOT)) {
        // TODO: TrieDb does not calculate receipts root correctly before the
        // BYZANTIUM fork. However, for empty receipts our receipts root
        // calculation is correct.
        //
        // On monad, the receipts root input is always null. On replay, we set
        // our receipts root to any non-null header input so our eth header is
        // correct in the Db.
        complete_header.receipts_root = receipts_root();
    }
    complete_header.state_root = state_root();
    complete_header.withdrawals_root = withdrawals_root();
    complete_header.transactions_root = transactions_root();
    complete_header.gas_used = receipts.empty() ? 0 : receipts.back().gas_used;
    complete_header.logs_bloom = compute_bloom(receipts);
    complete_header.ommers_hash = compute_ommers_hash(ommers);

    builder.add_block_header(complete_header);
    bool const enable_compaction = false;
    curr_root_ = db_.upsert(
        std::move(curr_root_),
        builder.build(prefix_),
        block_number_,
        enable_compaction);
}

void TrieDb::set_block_and_prefix(
    uint64_t const block_number, bytes32_t const &block_id)
{
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
    // no re-finalization
    auto const latest_finalized = db_.get_latest_finalized_version();
    MONAD_ASSERT_PRINTF(
        latest_finalized == INVALID_BLOCK_NUM ||
            block_number == latest_finalized + 1,
        "block_number %lu is not the next finalized block after %lu",
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
}

void TrieDb::update_verified_block(uint64_t const block_number)
{
    // no re-verification
    auto const latest_verified = db_.get_latest_verified_version();
    MONAD_ASSERT_PRINTF(
        latest_verified == INVALID_BLOCK_NUM || block_number > latest_verified,
        "block_number %lu must be greater than last_verified %lu",
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
                path.nibble_size() ==
                ((KECCAK256_SIZE + KECCAK256_SIZE) * 2 + 1)) {
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
            MONAD_DEBUG_ASSERT(!acct.has_error());

            auto const key = fmt::format("{}", NibblesView{path});

            json[key]["address"] = fmt::format("{}", acct.value().first);
            json[key]["balance"] =
                fmt::format("{}", acct.value().second.balance);
            json[key]["nonce"] =
                fmt::format("0x{:x}", acct.value().second.nonce);

            auto const icode = db.read_code(acct.value().second.code_hash);
            MONAD_ASSERT(icode);
            json[key]["code"] =
                "0x" + evmc::hex({icode->code(), icode->size()});

            if (!json[key].contains("storage")) {
                json[key]["storage"] = nlohmann::json::object();
            }
        }

        void handle_storage(Node const &node)
        {
            MONAD_ASSERT(node.has_value());

            auto encoded_storage = node.value();

            auto const storage = decode_storage_db(encoded_storage);
            MONAD_DEBUG_ASSERT(!storage.has_error());

            auto const acct_key = fmt::format(
                "{}", NibblesView{path}.substr(0, KECCAK256_SIZE * 2));

            auto const key = fmt::format(
                "{}",
                NibblesView{path}.substr(
                    KECCAK256_SIZE * 2 + 1, KECCAK256_SIZE * 2));

            auto storage_data_json = nlohmann::json::object();
            storage_data_json["slot"] = fmt::format(
                "0x{:02x}",
                fmt::join(
                    std::as_bytes(std::span(storage.value().first.bytes)), ""));
            storage_data_json["value"] = fmt::format(
                "0x{:02x}",
                fmt::join(
                    std::as_bytes(std::span(storage.value().second.bytes)),
                    ""));
            json[acct_key]["storage"][key] = storage_data_json;
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
