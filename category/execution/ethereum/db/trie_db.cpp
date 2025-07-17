#include <category/core/assert.h>
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
    , block_number_{db.get_latest_finalized_version() == INVALID_BLOCK_NUM ? 0 : db.get_latest_finalized_version()}
    , proposal_block_id_{bytes32_t{}}
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
        stats_account_no_value();
        return std::nullopt;
    }
    stats_account_value();

    auto encoded_account = value.value();
    auto const acct = decode_account_db_ignore_address(encoded_account);
    MONAD_DEBUG_ASSERT(!acct.has_error());
    return acct.value();
}

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
        stats_storage_no_value();
        return {};
    }
    stats_storage_value();
    auto encoded_storage = value.value();
    auto const storage = decode_storage_db_ignore_slot(encoded_storage);
    MONAD_ASSERT(!storage.has_error());
    return to_bytes(storage.value());
};

vm::SharedIntercode TrieDb::read_code(bytes32_t const &code_hash)
{
    // TODO read intercode object
    auto const value = db_.get(
        concat(
            prefix_,
            CODE_NIBBLE,
            NibblesView{to_byte_string_view(code_hash.bytes)}),
        block_number_);
    if (!value.has_value()) {
        return vm::make_shared_intercode({});
    }
    return vm::make_shared_intercode(value.assume_value());
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

    MONAD_ASSERT(block_id != bytes32_t{});
    if (db_.is_on_disk() && block_id != proposal_block_id_) {
        auto const dest_prefix = proposal_prefix(block_id);
        if (db_.get_latest_version() != INVALID_BLOCK_NUM) {
            MONAD_ASSERT(header.number != block_number_);
            db_.copy_trie(
                block_number_, prefix_, header.number, dest_prefix, false);
        }
        proposal_block_id_ = block_id;
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
    for (auto const &[hash, icode] : code) {
        // TODO write intercode object
        MONAD_ASSERT(icode);
        code_updates.push_front(update_alloc_.emplace_back(Update{
            .key = NibblesView{to_byte_string_view(hash.bytes)},
            .value = {{icode->code(), icode->code_size()}},
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
    MONAD_ASSERT(receipts.size() <= std::numeric_limits<uint32_t>::max());
    auto const &encoded_block_number =
        bytes_alloc_.emplace_back(rlp::encode_unsigned(header.number));
    std::vector<byte_string> index_alloc;
    index_alloc.reserve(std::max(
        receipts.size(),
        withdrawals.transform(&std::vector<Withdrawal>::size).value_or(0)));
    size_t log_index_begin = 0;
    for (uint32_t i = 0; i < static_cast<uint32_t>(receipts.size()); ++i) {
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

        // Call frames
        std::span<CallFrame const> frames{call_frames[i]};
        byte_string_view frame_view =
            bytes_alloc_.emplace_back(rlp::encode_call_frames(frames));
        uint8_t chunk_index = 0;
        auto const call_frame_prefix =
            serialize_as_big_endian<sizeof(uint32_t)>(i);
        while (!frame_view.empty()) {
            byte_string_view chunk =
                frame_view.substr(0, mpt::MAX_VALUE_LEN_OF_LEAF);
            frame_view.remove_prefix(chunk.size());
            byte_string const chunk_key =
                byte_string{&chunk_index, sizeof(uint8_t)};
            call_frame_updates.push_front(update_alloc_.emplace_back(Update{
                .key = bytes_alloc_.emplace_back(call_frame_prefix + chunk_key),
                .value = chunk,
                .incarnation = false,
                .next = UpdateList{},
                .version = static_cast<int64_t>(block_number_)}));
            ++chunk_index;
        }
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
    updates.push_front(state_update);
    updates.push_front(code_update);
    updates.push_front(receipt_update);
    updates.push_front(call_frame_update);
    updates.push_front(transaction_update);
    updates.push_front(ommer_update);
    updates.push_front(tx_hash_update);
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

void TrieDb::set_block_and_prefix(
    uint64_t const block_number, bytes32_t const &block_id)
{
    // set read state
    if (!db_.is_on_disk()) {
        MONAD_ASSERT(block_number_ == 0);
        MONAD_ASSERT(proposal_block_id_ == bytes32_t{});
        return;
    }
    prefix_ =
        block_id == bytes32_t{} ? finalized_nibbles : proposal_prefix(block_id);
    MONAD_ASSERT_PRINTF(
        db_.find(prefix_, block_number).has_value(),
        "Fail to find block_number %lu, block_id %s",
        block_number,
        evmc::hex(to_byte_string_view(block_id.bytes)).c_str());
    block_number_ = block_number;
    proposal_block_id_ = block_id;
}

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
    auto const src_prefix = proposal_prefix(block_id);
    if (db_.is_on_disk()) {
        MONAD_ASSERT(db_.find(src_prefix, block_number).has_value());
    }
    db_.copy_trie(
        block_number, src_prefix, block_number, finalized_nibbles, true);
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

            auto const icode = db.read_code(acct.value().second.code_hash);
            MONAD_ASSERT(icode);
            json[key]["code"] =
                "0x" + evmc::hex({icode->code(), icode->code_size()});

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
