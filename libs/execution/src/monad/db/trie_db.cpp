#include <monad/config.hpp>
#include <monad/core/account.hpp>
#include <monad/core/address.hpp>
#include <monad/core/assert.h>
#include <monad/core/byte_string.hpp>
#include <monad/core/bytes.hpp>
#include <monad/core/fmt/address_fmt.hpp> // NOLINT
#include <monad/core/fmt/bytes_fmt.hpp> // NOLINT
#include <monad/core/fmt/int_fmt.hpp> // NOLINT
#include <monad/core/keccak.h>
#include <monad/core/keccak.hpp>
#include <monad/core/receipt.hpp>
#include <monad/core/rlp/address_rlp.hpp>
#include <monad/core/rlp/block_rlp.hpp>
#include <monad/core/rlp/bytes_rlp.hpp>
#include <monad/core/rlp/int_rlp.hpp>
#include <monad/core/rlp/monad_block_rlp.hpp>
#include <monad/core/rlp/receipt_rlp.hpp>
#include <monad/core/rlp/transaction_rlp.hpp>
#include <monad/core/rlp/withdrawal_rlp.hpp>
#include <monad/db/trie_db.hpp>
#include <monad/db/util.hpp>
#include <monad/execution/trace/call_tracer.hpp>
#include <monad/execution/trace/rlp/call_frame_rlp.hpp>
#include <monad/execution/validate_block.hpp>
#include <monad/mpt/db.hpp>
#include <monad/mpt/nibbles_view.hpp>
#include <monad/mpt/nibbles_view_fmt.hpp> // NOLINT
#include <monad/mpt/node.hpp>
#include <monad/mpt/traverse.hpp>
#include <monad/mpt/update.hpp>
#include <monad/mpt/util.hpp>
#include <monad/rlp/encode2.hpp>
#include <monad/state2/state_deltas.hpp>
#include <monad/types/incarnation.hpp>
#include <monad/vm/evmone/code_analysis.hpp>

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

namespace
{
    byte_string
    encode_receipt_db(Receipt const &receipt, size_t const log_index_begin)
    {
        return rlp::encode_list2(
            rlp::encode_string2(rlp::encode_receipt(receipt)),
            rlp::encode_unsigned(log_index_begin));
    }

    byte_string encode_transaction_db(
        byte_string_view const encoded_tx, Address const &sender)
    {
        return rlp::encode_list2(
            rlp::encode_string2(encoded_tx), rlp::encode_address(sender));
    }
}

TrieDb::TrieDb(mpt::Db &db)
    : db_{db}
    , block_number_{db.get_latest_finalized_block_id() == INVALID_BLOCK_ID ? 0 : db.get_latest_finalized_block_id()}
    , round_number_{std::nullopt}
    , prefix_{finalized_nibbles}
{
}

TrieDb::~TrieDb() = default;

std::optional<Account> TrieDb::read_account(Address const &addr)
{
    auto const value = db_.get(
        concat(
            prefix_,
            STATE_NIBBLE,
            NibblesView{keccak256({addr.bytes, sizeof(addr.bytes)})}),
        block_number_);
    if (!value.has_value()) {
        return std::nullopt;
    }

    auto encoded_account = value.value();
    auto const acct = decode_account_db_ignore_address(encoded_account);
    MONAD_DEBUG_ASSERT(!acct.has_error());
    return acct.value();
}

#define MONAD_TRIEDB_STATS
#ifdef MONAD_TRIEDB_STATS
    #define STATS_STORAGE_NO_VALUE() stats_storage_no_value()
    #define STATS_STORAGE_VALUE() stats_storage_value()
#else
    #define STATS_STORAGE_NO_VALUE()
    #define STATS_STORAGE_VALUE()
#endif

bytes32_t
TrieDb::read_storage(Address const &addr, Incarnation, bytes32_t const &key)
{
    auto const value = db_.get(
        concat(
            prefix_,
            STATE_NIBBLE,
            NibblesView{keccak256({addr.bytes, sizeof(addr.bytes)})},
            NibblesView{keccak256({key.bytes, sizeof(key.bytes)})}),
        block_number_);
    if (!value.has_value()) {
        STATS_STORAGE_NO_VALUE();
        return {};
    }
    STATS_STORAGE_VALUE();
    auto encoded_storage = value.value();
    auto const storage = decode_storage_db_ignore_slot(encoded_storage);
    MONAD_ASSERT(!storage.has_error());
    return to_bytes(storage.value());
};

#ifdef MONAD_TRIEDB_STATS
    #undef STATS_STORAGE_NO_VALUE
    #undef STATS_STORAGE_VALUE
#endif

std::shared_ptr<CodeAnalysis> TrieDb::read_code(bytes32_t const &code_hash)
{
    // TODO read code analysis object
    auto const value = db_.get(
        concat(
            prefix_,
            CODE_NIBBLE,
            NibblesView{to_byte_string_view(code_hash.bytes)}),
        block_number_);
    if (!value.has_value()) {
        return std::make_shared<CodeAnalysis>(analyze({}));
    }
    return std::make_shared<CodeAnalysis>(analyze(value.assume_value()));
}

void TrieDb::commit(
    StateDeltas const &state_deltas, Code const &code,
    MonadConsensusBlockHeader const &consensus_header,
    std::vector<Receipt> const &receipts,
    std::vector<std::vector<CallFrame>> const &call_frames,
    std::vector<Address> const &senders,
    std::vector<Transaction> const &transactions,
    std::vector<BlockHeader> const &ommers,
    std::optional<std::vector<Withdrawal>> const &withdrawals)
{
    auto const &header = consensus_header.execution_inputs;
    MONAD_ASSERT(header.number <= std::numeric_limits<int64_t>::max());

    auto const parent_hash = [&]() {
        if (MONAD_UNLIKELY(header.number == 0)) {
            return bytes32_t{};
        }
        else {
            auto const n = db_.is_on_disk() ? header.number - 1 : 0;
            auto const parent_header_encoded =
                db_.get(concat(prefix_, BLOCKHEADER_NIBBLE), n);
            MONAD_ASSERT(parent_header_encoded.has_value());
            return to_bytes(keccak256(parent_header_encoded.value()));
        }
    }();

    if (db_.is_on_disk() && (consensus_header.round != round_number_ ||
                             header.number != block_number_)) {
        auto const dest_prefix = proposal_prefix(consensus_header.round);
        if (db_.get_latest_block_id() != INVALID_BLOCK_ID) {
            db_.copy_trie(
                block_number_, prefix_, header.number, dest_prefix, false);
        }
        round_number_ = consensus_header.round;
        block_number_ = header.number;
        prefix_ = dest_prefix;
    }

    UpdateList account_updates;
    for (auto const &[addr, delta] : state_deltas) {
        UpdateList storage_updates;
        std::optional<byte_string_view> value;
        auto const &account = delta.account.second;
        if (account.has_value()) {
            for (auto const &[key, delta] : delta.storage) {
                if (delta.first != delta.second) {
                    storage_updates.push_front(
                        update_alloc_.emplace_back(Update{
                            .key = hash_alloc_.emplace_back(
                                keccak256({key.bytes, sizeof(key.bytes)})),
                            .value = delta.second == bytes32_t{}
                                         ? std::nullopt
                                         : std::make_optional<byte_string_view>(
                                               bytes_alloc_.emplace_back(
                                                   encode_storage_db(
                                                       key, delta.second))),
                            .incarnation = false,
                            .next = UpdateList{},
                            .version = static_cast<int64_t>(block_number_)}));
                }
            }
            value = bytes_alloc_.emplace_back(
                encode_account_db(addr, account.value()));
        }

        if (!storage_updates.empty() || delta.account.first != account) {
            bool const incarnation =
                account.has_value() && delta.account.first.has_value() &&
                delta.account.first->incarnation != account->incarnation;
            account_updates.push_front(update_alloc_.emplace_back(Update{
                .key = hash_alloc_.emplace_back(
                    keccak256({addr.bytes, sizeof(addr.bytes)})),
                .value = value,
                .incarnation = incarnation,
                .next = std::move(storage_updates),
                .version = static_cast<int64_t>(block_number_)}));
        }
    }

    UpdateList code_updates;
    for (auto const &[hash, code_analysis] : code) {
        // TODO write code analysis object
        MONAD_ASSERT(code_analysis);
        code_updates.push_front(update_alloc_.emplace_back(Update{
            .key = NibblesView{to_byte_string_view(hash.bytes)},
            .value = code_analysis->executable_code(),
            .incarnation = false,
            .next = UpdateList{},
            .version = static_cast<int64_t>(block_number_)}));
    }

    UpdateList receipt_updates;
    UpdateList transaction_updates;
    UpdateList tx_hash_updates;
    UpdateList call_frame_updates;
    MONAD_ASSERT(receipts.size() == transactions.size());
    MONAD_ASSERT(transactions.size() == senders.size());
    MONAD_ASSERT(receipts.size() == call_frames.size());
    auto const &encoded_block_number =
        bytes_alloc_.emplace_back(rlp::encode_unsigned(header.number));
    std::vector<byte_string> index_alloc;
    index_alloc.reserve(std::max(
        receipts.size(),
        withdrawals.transform(&std::vector<Withdrawal>::size).value_or(0)));
    size_t log_index_begin = 0;
    for (size_t i = 0; i < receipts.size(); ++i) {
        auto const &rlp_index =
            index_alloc.emplace_back(rlp::encode_unsigned(i));
        auto const &receipt = receipts[i];
        auto const &encoded_receipt = bytes_alloc_.emplace_back(
            encode_receipt_db(receipt, log_index_begin));
        log_index_begin += receipt.logs.size();
        receipt_updates.push_front(update_alloc_.emplace_back(Update{
            .key = NibblesView{rlp_index},
            .value = encoded_receipt,
            .incarnation = false,
            .next = UpdateList{},
            .version = static_cast<int64_t>(block_number_)}));

        auto const encoded_tx = rlp::encode_transaction(transactions[i]);
        transaction_updates.push_front(update_alloc_.emplace_back(Update{
            .key = NibblesView{rlp_index},
            .value = bytes_alloc_.emplace_back(
                encode_transaction_db(encoded_tx, senders[i])),
            .incarnation = false,
            .next = UpdateList{},
            .version = static_cast<int64_t>(block_number_)}));
        tx_hash_updates.push_front(update_alloc_.emplace_back(Update{
            .key = NibblesView{hash_alloc_.emplace_back(keccak256(encoded_tx))},
            .value = bytes_alloc_.emplace_back(
                rlp::encode_list2(encoded_block_number, rlp_index)),
            .incarnation = false,
            .next = UpdateList{},
            .version = static_cast<int64_t>(block_number_)}));

        std::span<CallFrame const> frames{call_frames[i]};
        // TODO: a better way to ensure node size is <= 256 MB
        if (frames.size() > 100) {
            frames = frames.first(100);
        }
        call_frame_updates.push_front(update_alloc_.emplace_back(Update{
            .key = NibblesView{rlp_index},
            .value = bytes_alloc_.emplace_back(rlp::encode_call_frames(frames)),
            .incarnation = false,
            .next = UpdateList{},
            .version = static_cast<int64_t>(block_number_)}));
    }

    UpdateList updates;

    auto state_update = Update{
        .key = state_nibbles,
        .value = byte_string_view{},
        .incarnation = false,
        .next = std::move(account_updates),
        .version = static_cast<int64_t>(block_number_)};
    auto code_update = Update{
        .key = code_nibbles,
        .value = byte_string_view{},
        .incarnation = false,
        .next = std::move(code_updates),
        .version = static_cast<int64_t>(block_number_)};
    auto receipt_update = Update{
        .key = receipt_nibbles,
        .value = byte_string_view{},
        .incarnation = true,
        .next = std::move(receipt_updates),
        .version = static_cast<int64_t>(block_number_)};
    auto call_frame_update = Update{
        .key = call_frame_nibbles,
        .value = byte_string_view{},
        .incarnation = true,
        .next = std::move(call_frame_updates),
        .version = static_cast<int64_t>(block_number_)};
    auto transaction_update = Update{
        .key = transaction_nibbles,
        .value = byte_string_view{},
        .incarnation = true,
        .next = std::move(transaction_updates),
        .version = static_cast<int64_t>(block_number_)};
    auto ommer_update = Update{
        .key = ommer_nibbles,
        .value = bytes_alloc_.emplace_back(rlp::encode_ommers(ommers)),
        .incarnation = true,
        .next = UpdateList{},
        .version = static_cast<int64_t>(block_number_)};
    auto tx_hash_update = Update{
        .key = tx_hash_nibbles,
        .value = byte_string_view{},
        .incarnation = false,
        .next = std::move(tx_hash_updates),
        .version = static_cast<int64_t>(block_number_)};
    auto bft_block_update = Update{
        .key = bft_block_nibbles,
        .value = bytes_alloc_.emplace_back(
            rlp::encode_consensus_block_header(consensus_header)),
        .incarnation = true,
        .next = UpdateList{},
        .version = static_cast<int64_t>(block_number_)};
    updates.push_front(state_update);
    updates.push_front(code_update);
    updates.push_front(receipt_update);
    updates.push_front(call_frame_update);
    updates.push_front(transaction_update);
    updates.push_front(ommer_update);
    updates.push_front(tx_hash_update);
    updates.push_front(bft_block_update);
    UpdateList withdrawal_updates;
    if (withdrawals.has_value()) {
        // only commit withdrawals when the optional has value
        for (size_t i = 0; i < withdrawals.value().size(); ++i) {
            if (i >= index_alloc.size()) {
                index_alloc.emplace_back(rlp::encode_unsigned(i));
            }
            withdrawal_updates.push_front(update_alloc_.emplace_back(Update{
                .key = NibblesView{index_alloc[i]},
                .value = bytes_alloc_.emplace_back(
                    rlp::encode_withdrawal(withdrawals.value()[i])),
                .incarnation = false,
                .next = UpdateList{},
                .version = static_cast<int64_t>(block_number_)}));
        }
        updates.push_front(update_alloc_.emplace_back(Update{
            .key = withdrawal_nibbles,
            .value = byte_string_view{},
            .incarnation = true,
            .next = std::move(withdrawal_updates),
            .version = static_cast<int64_t>(block_number_)}));
    }

    UpdateList ls;
    ls.push_front(update_alloc_.emplace_back(Update{
        .key = prefix_,
        .value = byte_string_view{},
        .incarnation = false,
        .next = std::move(updates),
        .version = static_cast<int64_t>(block_number_)}));

    db_.upsert(std::move(ls), block_number_, true, true, false);

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
    complete_header.parent_hash = parent_hash;
    complete_header.gas_used = receipts.empty() ? 0 : receipts.back().gas_used;
    complete_header.logs_bloom = compute_bloom(receipts);
    complete_header.ommers_hash = compute_ommers_hash(ommers);

    auto const eth_header_rlp = rlp::encode_block_header(complete_header);

    UpdateList block_hash_nested_updates;
    block_hash_nested_updates.push_front(update_alloc_.emplace_back(Update{
        .key = hash_alloc_.emplace_back(keccak256(eth_header_rlp)),
        .value = encoded_block_number,
        .incarnation = false,
        .next = UpdateList{},
        .version = static_cast<int64_t>(block_number_)}));

    UpdateList updates2;

    auto block_header_update = Update{
        .key = block_header_nibbles,
        .value = eth_header_rlp,
        .incarnation = true,
        .next = UpdateList{},
        .version = static_cast<int64_t>(block_number_)};
    auto block_hash_update = Update{
        .key = block_hash_nibbles,
        .value = byte_string_view{},
        .incarnation = false,
        .next = std::move(block_hash_nested_updates),
        .version = static_cast<int64_t>(block_number_)};

    updates2.push_front(block_header_update);
    updates2.push_front(block_hash_update);

    UpdateList ls2;
    ls2.push_front(update_alloc_.emplace_back(Update{
        .key = prefix_,
        .value = byte_string_view{},
        .incarnation = false,
        .next = std::move(updates2),
        .version = static_cast<int64_t>(block_number_)}));

    bool const enable_compaction = false;
    db_.upsert(std::move(ls2), block_number_, enable_compaction);

    update_alloc_.clear();
    bytes_alloc_.clear();
    hash_alloc_.clear();
}

void TrieDb::set_block_and_round(
    uint64_t const block_number, std::optional<uint64_t> const round_number)
{
    // set read state
    if (!db_.is_on_disk()) {
        MONAD_ASSERT(block_number_ == 0);
        MONAD_ASSERT(round_number_ == std::nullopt);
        return;
    }
    prefix_ = round_number.has_value() ? proposal_prefix(round_number.value())
                                       : finalized_nibbles;
    MONAD_ASSERT(db_.find(prefix_, block_number).has_value());
    block_number_ = block_number;
    round_number_ = round_number;
}

void TrieDb::finalize(uint64_t const block_number, uint64_t const round_number)
{
    // no re-finalization
    if (db_.is_on_disk()) {
#if 0 // TODO: re-enable this when we remove double finalization
        auto const latest_finalized = db_.get_latest_finalized_block_id();
        MONAD_ASSERT(
            latest_finalized == INVALID_BLOCK_ID ||
            block_number == latest_finalized + 1);
#endif
        auto const src_prefix = proposal_prefix(round_number);
        MONAD_ASSERT(db_.find(src_prefix, block_number).has_value());
        db_.copy_trie(
            block_number, src_prefix, block_number, finalized_nibbles, true);
        db_.update_finalized_block(block_number);
    }
}

void TrieDb::update_verified_block(uint64_t const block_number)
{
    // no re-verification
    if (db_.is_on_disk()) {
#if 0 // TODO: re-enable this when we remove double finalization
        auto const latest_verified = db_.get_latest_verified_block_id();
        MONAD_ASSERT(
            latest_verified == INVALID_BLOCK_ID ||
            block_number == latest_verified + 1);
#endif
        db_.update_verified_block(block_number);
    }
}

void TrieDb::update_voted_metadata(
    uint64_t const block_number, uint64_t const round)
{
    auto const latest_voted_round = db_.get_latest_voted_round();
    if (MONAD_LIKELY(
            round > latest_voted_round ||
            latest_voted_round == INVALID_ROUND_NUM)) {
        db_.update_voted_metadata(block_number, round);
    }
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
    auto const value =
        db_.get_data(concat(prefix_, WITHDRAWAL_NIBBLE), block_number_);
    if (value.has_error()) {
        return std::nullopt;
    }
    if (value.value().empty()) {
        return NULL_ROOT;
    }
    MONAD_ASSERT(value.value().size() == sizeof(bytes32_t));
    return to_bytes(value.value());
}

bytes32_t TrieDb::merkle_root(mpt::Nibbles const &nibbles)
{
    auto const value =
        db_.get_data(concat(prefix_, NibblesView{nibbles}), block_number_);
    if (!value.has_value() || value.value().empty()) {
        return NULL_ROOT;
    }
    MONAD_ASSERT(value.value().size() == sizeof(bytes32_t));
    return to_bytes(value.value());
}

BlockHeader TrieDb::read_eth_header()
{
    auto const query_res =
        db_.get(concat(prefix_, BLOCKHEADER_NIBBLE), block_number_);
    MONAD_ASSERT(!query_res.has_error());
    auto encoded_header_db = query_res.value();
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
        "{:6} {:6}",
        n_storage_no_value_.load(std::memory_order_acquire),
        n_storage_value_.load(std::memory_order_acquire));
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
            MONAD_DEBUG_ASSERT(!acct.has_error());

            auto const key = fmt::format("{}", NibblesView{path});

            json[key]["address"] = fmt::format("{}", acct.value().first);
            json[key]["balance"] =
                fmt::format("{}", acct.value().second.balance);
            json[key]["nonce"] =
                fmt::format("0x{:x}", acct.value().second.nonce);

            auto const code_analysis =
                db.read_code(acct.value().second.code_hash);
            MONAD_ASSERT(code_analysis);
            json[key]["code"] =
                "0x" + evmc::hex(code_analysis->executable_code());

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
                    KECCAK256_SIZE * 2, KECCAK256_SIZE * 2));

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

    auto res_cursor = db_.find(concat(prefix_, STATE_NIBBLE), block_number_);
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

size_t TrieDb::prefetch_current_root()
{
    return db_.prefetch();
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
