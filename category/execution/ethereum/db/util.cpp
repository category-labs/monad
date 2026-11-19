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
#include <category/core/int.hpp>
#include <category/core/likely.h>
#include <category/core/log.hpp>
#include <category/core/result.hpp>
#include <category/core/rlp/decode_error.hpp>
#include <category/core/runtime/unaligned.hpp>
#include <category/execution/ethereum/core/account.hpp>
#include <category/execution/ethereum/core/block.hpp>
#include <category/execution/ethereum/core/receipt.hpp>
#include <category/execution/ethereum/core/rlp/account_rlp.hpp>
#include <category/execution/ethereum/core/rlp/address_rlp.hpp>
#include <category/execution/ethereum/core/rlp/block_rlp.hpp>
#include <category/execution/ethereum/core/rlp/bytes_rlp.hpp>
#include <category/execution/ethereum/core/rlp/int_rlp.hpp>
#include <category/execution/ethereum/core/rlp/receipt_rlp.hpp>
#include <category/execution/ethereum/core/rlp/transaction_rlp.hpp>
#include <category/execution/ethereum/core/transaction.hpp>
#include <category/execution/ethereum/db/util.hpp>
#include <category/execution/ethereum/rlp/decode.hpp>
#include <category/execution/ethereum/rlp/encode2.hpp>
#include <category/execution/monad/db/storage_page.hpp>
#include <category/mpt/compute.hpp>
#include <category/mpt/db.hpp>
#include <category/mpt/db_error.hpp>
#include <category/mpt/nibbles_view.hpp>
#include <category/mpt/node.hpp>
#include <category/mpt/ondisk_db_config.hpp>
#include <category/mpt/state_machine.hpp>
#include <category/mpt/state_machine_kind.hpp>
#include <category/mpt/traverse.hpp>
#include <category/mpt/traverse_util.hpp>
#include <category/mpt/update.hpp>
#include <category/mpt/util.hpp>

#include <boost/outcome/try.hpp>

#include <nlohmann/json.hpp>

#include <quill/std/Chrono.h>

#include <algorithm>
#include <chrono>
#include <cstddef>
#include <cstdint>
#include <filesystem>
#include <fstream>
#include <functional>
#include <memory>
#include <optional>
#include <string>
#include <utility>
#include <vector>

MONAD_NAMESPACE_BEGIN

using namespace monad::mpt;

namespace
{
    bytes32_t to_bytes32(Nibbles const &nibbles)
    {
        MONAD_ASSERT(nibbles.nibble_size() == sizeof(bytes32_t) * 2);
        if (nibbles.begin_nibble()) { // not left-aligned
            Nibbles const compact_nibbles = nibbles.substr(0);
            MONAD_ASSERT(compact_nibbles.data_size() == sizeof(bytes32_t));
            return to_bytes(byte_string_view{
                compact_nibbles.data(), compact_nibbles.data_size()});
        }
        MONAD_ASSERT(nibbles.data_size() == sizeof(bytes32_t));
        return to_bytes(byte_string_view{nibbles.data(), nibbles.data_size()});
    }

    struct PagedStorageLeafProcessor
    {
        static byte_string process(Node const &node)
        {
            MONAD_ASSERT(node.has_value());
            auto const page = decode_storage_leaf_to_page(node.value(), true);
            auto const commitment = page_commit(page);
            return rlp::encode_string2(
                {commitment.bytes, sizeof(commitment.bytes)});
        }
    };

    Result<byte_string_view>
    parse_encoded_receipt_ignore_log_index(byte_string_view &enc)
    {
        BOOST_OUTCOME_TRY(enc, rlp::parse_list_metadata(enc));
        return rlp::decode_string(enc);
    }

    struct ReceiptLeafProcessor
    {
        static byte_string_view process(mpt::Node const &node)
        {
            byte_string_view leaf_value = node.value();
            auto const enc_receipt =
                parse_encoded_receipt_ignore_log_index(leaf_value);
            MONAD_ASSERT(!enc_receipt.has_error());
            return enc_receipt.value();
        }
    };

    Result<byte_string_view>
    parse_encoded_transaction_ignore_sender(byte_string_view &enc)
    {
        BOOST_OUTCOME_TRY(enc, rlp::parse_list_metadata(enc));
        return rlp::decode_string(enc);
    }

    struct TransactionLeafProcessor
    {
        static byte_string_view process(mpt::Node const &node)
        {
            byte_string_view leaf_value = node.value();
            auto const enc_transaction =
                parse_encoded_transaction_ignore_sender(leaf_value);
            MONAD_ASSERT(!enc_transaction.has_error());
            return enc_transaction.value();
        }
    };

    using AccountMerkleCompute = MerkleComputeBase<AccountLeafProcessor>;
    using StorageMerkleCompute = MerkleComputeBase<StorageLeafProcessor>;
    using PagedStorageMerkleCompute =
        MerkleComputeBase<PagedStorageLeafProcessor>;

    template <typename Base>
    struct StorageRootMerkleComputeImpl : public Base
    {
        virtual unsigned
        compute(unsigned char *const buffer, Node const &node) override
        {
            MONAD_ASSERT(node.has_value());
            return encode_two_pieces_reference(
                buffer,
                node.path_nibble_view(),
                AccountLeafProcessor::process(node),
                true);
        }
    };

    using StorageRootMerkleCompute =
        StorageRootMerkleComputeImpl<StorageMerkleCompute>;
    using PagedStorageRootMerkleCompute =
        StorageRootMerkleComputeImpl<PagedStorageMerkleCompute>;

    struct AccountRootMerkleCompute : public AccountMerkleCompute
    {
        virtual unsigned compute(unsigned char *const, Node const &) override
        {
            return 0;
        }
    };

    Result<Account> decode_account_db_helper(byte_string_view &payload)
    {
        Account acct;
        BOOST_OUTCOME_TRY(
            auto const incarnation, rlp::decode_unsigned<uint64_t>(payload));
        acct.incarnation = Incarnation::from_int(incarnation);
        BOOST_OUTCOME_TRY(acct.nonce, rlp::decode_unsigned<uint64_t>(payload));
        BOOST_OUTCOME_TRY(
            acct.balance, rlp::decode_unsigned<uint256_t>(payload));
        if (!payload.empty()) {
            BOOST_OUTCOME_TRY(acct.code_hash, rlp::decode_bytes32(payload));
        }
        if (MONAD_UNLIKELY(!payload.empty())) {
            return rlp::DecodeError::InputTooLong;
        }
        return acct;
    }
}

constexpr uint8_t MachineBase::prefix_len() const
{
    return trie_section == TrieType::Proposal ? PROPOSAL_PREFIX_LEN
                                              : FINALIZED_PREFIX_LEN;
}

mpt::Compute &MachineBase::get_compute() const
{
    static EmptyCompute empty_compute;

    static AccountMerkleCompute account_compute;
    static AccountRootMerkleCompute account_root_compute;

    static VarLenMerkleCompute generic_merkle_compute;
    static RootVarLenMerkleCompute generic_root_merkle_compute;

    static VarLenMerkleCompute<ReceiptLeafProcessor> receipt_compute;
    static RootVarLenMerkleCompute<ReceiptLeafProcessor> receipt_root_compute;
    static VarLenMerkleCompute<TransactionLeafProcessor> transaction_compute;
    static RootVarLenMerkleCompute<TransactionLeafProcessor>
        transaction_root_compute;

    auto const prefix_length = prefix_len();
    if (MONAD_LIKELY(table == TableType::State)) {
        MONAD_ASSERT(depth >= prefix_length);
        if (MONAD_UNLIKELY(depth == prefix_length)) {
            return account_root_compute;
        }
        else if (depth < prefix_length + 2 * sizeof(bytes32_t)) {
            return account_compute;
        }
        else if (depth == prefix_length + 2 * sizeof(bytes32_t)) {
            return storage_root_compute();
        }
        else {
            return storage_compute();
        }
    }
    else if (table == TableType::Receipt) {
        return depth == prefix_length ? receipt_root_compute : receipt_compute;
    }
    else if (table == TableType::Transaction) {
        return depth == prefix_length ? transaction_root_compute
                                      : transaction_compute;
    }
    else if (table == TableType::Withdrawal) {
        return depth == prefix_length ? generic_root_merkle_compute
                                      : generic_merkle_compute;
    }
    else {
        return empty_compute;
    }
}

bool MachineBase::is_variable_length() const
{
    return depth > prefix_len() &&
           (table == TableType::Transaction || table == TableType::Receipt ||
            table == TableType::Withdrawal || table == TableType::CallFrame);
}

void MachineBase::down(unsigned char const nibble)
{
    ++depth;
    if (depth == TOP_NIBBLE_PREFIX_LEN) {
        MONAD_ASSERT(trie_section == TrieType::Undefined);
        MONAD_ASSERT(table == TableType::Prefix);
        if (nibble == PROPOSAL_NIBBLE) {
            trie_section = TrieType::Proposal;
        }
        else {
            MONAD_ASSERT(nibble == FINALIZED_NIBBLE);
            trie_section = TrieType::Finalized;
        }
        return;
    }
    MONAD_ASSERT(trie_section != TrieType::Undefined);
    auto const prefix_length = prefix_len();
    MONAD_ASSERT(depth <= max_depth(prefix_length));
    if (MONAD_UNLIKELY(depth == prefix_length)) {
        MONAD_ASSERT(table == TableType::Prefix);
        MONAD_ASSERT_PRINTF(
            nibble <= CALL_FRAME_NIBBLE,
            "Invalid nibble %u",
            static_cast<unsigned>(nibble));
        table = static_cast<TableType>(nibble + 1);
    }
}

// Equivalent to down() on each nibble: only the trie-section and table nibbles
// change state other than depth.
void MachineBase::down(mpt::NibblesView const path)
{
    auto const n = static_cast<unsigned>(path.nibble_size());
    unsigned i = 0;
    if (MONAD_UNLIKELY(depth < TOP_NIBBLE_PREFIX_LEN) && i < n) {
        MachineBase::down(path.get(i++));
    }
    if (i == n) {
        return;
    }
    MONAD_ASSERT(trie_section != TrieType::Undefined);
    auto const prefix_length = prefix_len();
    if (MONAD_UNLIKELY(depth < prefix_length)) {
        auto const table_nibble =
            i + static_cast<unsigned>(prefix_length - depth) - 1;
        if (table_nibble < n) {
            depth = static_cast<uint8_t>(depth + (table_nibble - i));
            i = table_nibble;
            MachineBase::down(path.get(i++));
        }
    }
    auto const new_depth = depth + (n - i);
    MONAD_ASSERT(new_depth <= max_depth(prefix_length));
    depth = static_cast<uint8_t>(new_depth);
}

void MachineBase::up(size_t const n)
{
    MONAD_ASSERT(n <= depth);
    depth -= static_cast<uint8_t>(n);
    if (MONAD_UNLIKELY(depth < prefix_len())) {
        table = TableType::Prefix;
    }
    if (MONAD_UNLIKELY(depth < TOP_NIBBLE_PREFIX_LEN)) {
        trie_section = TrieType::Undefined;
    }
}

mpt::Compute &MachineBase::storage_compute() const
{
    static StorageMerkleCompute compute;
    return compute;
}

mpt::Compute &MachineBase::storage_root_compute() const
{
    static StorageRootMerkleCompute compute;
    return compute;
}

mpt::state_machine_kind InMemoryMachine::kind() const
{
    return mpt::state_machine_kind::ethereum;
}

bool InMemoryMachine::cache() const
{
    return true;
}

bool InMemoryMachine::compact() const
{
    return false;
}

std::unique_ptr<StateMachine> InMemoryMachine::clone() const
{
    return std::make_unique<InMemoryMachine>(*this);
}

mpt::state_machine_kind MonadInMemoryMachine::kind() const
{
    return mpt::state_machine_kind::monad;
}

std::unique_ptr<StateMachine> MonadInMemoryMachine::clone() const
{
    return std::make_unique<MonadInMemoryMachine>(*this);
}

mpt::Compute &MonadInMemoryMachine::storage_compute() const
{
    static PagedStorageMerkleCompute compute;
    return compute;
}

mpt::Compute &MonadInMemoryMachine::storage_root_compute() const
{
    static PagedStorageRootMerkleCompute compute;
    return compute;
}

mpt::state_machine_kind OnDiskMachine::kind() const
{
    return mpt::state_machine_kind::ethereum;
}

bool OnDiskMachine::cache() const
{
    constexpr uint64_t CACHE_DEPTH_IN_TABLE = 5;
    return table == TableType::Prefix ||
           ((depth <= prefix_len() + CACHE_DEPTH_IN_TABLE) &&
            (table == TableType::State || table == TableType::Code ||
             table == TableType::TxHash || table == TableType::BlockHash));
}

bool OnDiskMachine::compact() const
{
    return depth >= prefix_len();
}

bool OnDiskMachine::auto_expire() const
{
    return table == TableType::TxHash || table == TableType::BlockHash;
}

std::unique_ptr<StateMachine> OnDiskMachine::clone() const
{
    return std::make_unique<OnDiskMachine>(*this);
}

mpt::state_machine_kind MonadOnDiskMachine::kind() const
{
    return mpt::state_machine_kind::monad;
}

std::unique_ptr<StateMachine> MonadOnDiskMachine::clone() const
{
    return std::make_unique<MonadOnDiskMachine>(*this);
}

mpt::Compute &MonadOnDiskMachine::storage_compute() const
{
    static PagedStorageMerkleCompute compute;
    return compute;
}

mpt::Compute &MonadOnDiskMachine::storage_root_compute() const
{
    static PagedStorageRootMerkleCompute compute;
    return compute;
}

Result<std::pair<Receipt, size_t>> decode_receipt_db(byte_string_view &enc)
{
    BOOST_OUTCOME_TRY(
        auto encoded_receipt, parse_encoded_receipt_ignore_log_index(enc));
    BOOST_OUTCOME_TRY(auto const receipt, rlp::decode_receipt(encoded_receipt));
    BOOST_OUTCOME_TRY(
        auto const log_index_begin, rlp::decode_unsigned<size_t>(enc));
    if (MONAD_UNLIKELY(!enc.empty())) {
        return rlp::DecodeError::InputTooLong;
    }
    return std::make_pair(receipt, log_index_begin);
}

Result<std::pair<Transaction, Address>>
decode_transaction_db(byte_string_view &enc)
{
    BOOST_OUTCOME_TRY(
        auto encoded_tx, parse_encoded_transaction_ignore_sender(enc));
    BOOST_OUTCOME_TRY(
        auto const transaction, rlp::decode_transaction(encoded_tx));
    BOOST_OUTCOME_TRY(auto const sender, rlp::decode_address(enc));
    if (MONAD_UNLIKELY(!enc.empty())) {
        return rlp::DecodeError::InputTooLong;
    }
    return {transaction, sender};
}

byte_string encode_account_db(Address const &address, Account const &account)
{
    byte_string encoded_account;
    encoded_account += rlp::encode_address(address);
    encoded_account += rlp::encode_unsigned(account.incarnation.to_int());
    encoded_account += rlp::encode_unsigned(account.nonce);
    encoded_account += rlp::encode_unsigned(account.balance);
    if (account.code_hash != NULL_HASH) {
        encoded_account += rlp::encode_bytes32(account.code_hash);
    }
    return rlp::encode_list2(encoded_account);
}

Result<std::pair<byte_string_view, byte_string_view>>
decode_account_db_raw(byte_string_view &enc)
{
    BOOST_OUTCOME_TRY(auto payload, rlp::parse_list_metadata(enc));
    BOOST_OUTCOME_TRY(auto const address, rlp::parse_string_metadata(payload));
    if (MONAD_UNLIKELY(address.size() != sizeof(Address))) {
        return rlp::DecodeError::ArrayLengthUnexpected;
    }
    return {address, payload};
}

Result<std::pair<Address, Account>> decode_account_db(byte_string_view &enc)
{
    BOOST_OUTCOME_TRY(auto res, decode_account_db_raw(enc));
    Address const address = unaligned_load<Address>(res.first.data());
    BOOST_OUTCOME_TRY(auto const acct, decode_account_db_helper(res.second));
    return {address, acct};
}

Result<Account> decode_account_db_ignore_address(byte_string_view &enc)
{
    BOOST_OUTCOME_TRY(auto res, decode_account_db_raw(enc));
    return decode_account_db_helper(res.second);
}

byte_string encode_storage_db(bytes32_t const &key, bytes32_t const &val)
{
    byte_string encoded_storage;
    encoded_storage += rlp::encode_bytes32_compact(key);
    encoded_storage += rlp::encode_bytes32_compact(val);
    return rlp::encode_list2(encoded_storage);
}

byte_string
encode_storage_page_db(bytes32_t const &key, storage_page_t const &page)
{
    return rlp::encode_list2(
        rlp::encode_bytes32_compact(key),
        rlp::encode_string2(encode_storage_page(page)));
}

Result<std::pair<byte_string_view, byte_string_view>>
decode_storage_db_raw(byte_string_view &enc)
{
    BOOST_OUTCOME_TRY(auto payload, rlp::parse_list_metadata(enc));
    BOOST_OUTCOME_TRY(byte_string_view const slot, rlp::decode_string(payload));
    if (MONAD_UNLIKELY(slot.size() > sizeof(bytes32_t))) {
        return rlp::DecodeError::InputTooLong;
    }
    // The value is left unbounded: it is a bytes32 on the slot-encoded path but
    // a whole encoded page on the page-encoded one, so only the caller knows
    // its bound.
    BOOST_OUTCOME_TRY(byte_string_view const val, rlp::decode_string(payload));
    return {slot, val};
}

Result<std::pair<bytes32_t, bytes32_t>> decode_storage_db(byte_string_view &enc)
{
    BOOST_OUTCOME_TRY(auto const res, decode_storage_db_raw(enc));
    if (!enc.empty()) {
        return rlp::DecodeError::InputTooLong;
    }
    if (MONAD_UNLIKELY(res.second.size() > sizeof(bytes32_t))) {
        return rlp::DecodeError::InputTooLong;
    }
    return {to_bytes(res.first), to_bytes(res.second)};
}

Result<byte_string_view> decode_storage_db_ignore_key(byte_string_view &enc)
{
    BOOST_OUTCOME_TRY(auto const res, decode_storage_db_raw(enc));
    if (!enc.empty()) {
        return rlp::DecodeError::InputTooLong;
    }
    return res.second;
}

storage_page_t
decode_storage_leaf_to_page(byte_string_view encoded, bool const page_encoded)
{
    auto const value = decode_storage_db_ignore_key(encoded);
    MONAD_ASSERT(!value.has_error());
    if (!page_encoded) {
        return storage_page_t{to_bytes(value.value())};
    }
    auto const page = decode_storage_page(value.value());
    MONAD_ASSERT(!page.has_error());
    return page.value();
}

Result<DecodedStoragePage> decode_storage_page_leaf(byte_string_view leaf)
{
    BOOST_OUTCOME_TRY(auto const raw, decode_storage_db_raw(leaf));
    if (!leaf.empty()) {
        return rlp::DecodeError::InputTooLong;
    }
    auto const page_key = to_bytes(raw.first);
    // compute_slot_key shifts out the key's top PAGE_KEY_SHIFT bits, so a key
    // with any of them set yields slots that belong to a different page.
    if (MONAD_UNLIKELY(
            compute_page_key(compute_slot_key(page_key, 0)) != page_key)) {
        return rlp::DecodeError::NonCanonical;
    }
    BOOST_OUTCOME_TRY(auto page, decode_storage_page(raw.second));
    return DecodedStoragePage{page_key, std::move(page)};
}

byte_string AccountLeafProcessor::process(mpt::Node const &node)
{
    MONAD_ASSERT(node.has_value());

    // this is the block number leaf
    if (MONAD_UNLIKELY(node.value().empty())) {
        return {};
    }

    auto encoded_account = node.value();
    auto const acct = decode_account_db_ignore_address(encoded_account);
    MONAD_ASSERT(!acct.has_error());
    MONAD_ASSERT(encoded_account.empty());
    bytes32_t storage_root = NULL_ROOT;
    if (node.number_of_children()) {
        MONAD_ASSERT(node.data().size() == sizeof(bytes32_t));
        std::copy_n(node.data().data(), sizeof(bytes32_t), storage_root.bytes);
    }
    return rlp::encode_account(acct.value(), storage_root);
}

byte_string StorageLeafProcessor::process(mpt::Node const &node)
{
    MONAD_ASSERT(node.has_value());
    auto encoded_storage = node.value();
    auto const storage = decode_storage_db_ignore_key(encoded_storage);
    MONAD_ASSERT(!storage.has_error());
    return rlp::encode_string2(storage.value());
}

void write_to_file(
    nlohmann::json const &j, std::filesystem::path const &root_path,
    uint64_t const block_number)
{
    [[maybe_unused]] auto const start_time = std::chrono::steady_clock::now();

    auto const dir = root_path / std::to_string(block_number);
    std::filesystem::create_directory(dir);
    MONAD_ASSERT(std::filesystem::is_directory(dir));

    auto const file = dir / "state.json";
    MONAD_ASSERT(!std::filesystem::exists(file));
    std::ofstream ofile(file);
    ofile << j.dump(4);

    LOG_INFO(
        "Finished dumping to json file at block = {}, time elapsed = {}",
        block_number,
        std::chrono::duration_cast<std::chrono::milliseconds>(
            std::chrono::steady_clock::now() - start_time));
}

Node::SharedPtr
load_header(Node::SharedPtr root, mpt::Db &db, BlockHeader const &header)
{
    using namespace mpt;

    UpdateList header_updates;
    UpdateList ls;
    auto const n = db.is_on_disk() ? header.number : 0;
    auto const header_encoded = rlp::encode_block_header(header);

    Update block_header_update{
        .key = block_header_nibbles,
        .value = header_encoded,
        .incarnation = true,
        .next = mpt::UpdateList{},
        .version = static_cast<int64_t>(n)};
    header_updates.push_front(block_header_update);
    mpt::Update u{
        .key = finalized_nibbles,
        .value = byte_string_view{},
        .incarnation = false,
        .next = std::move(header_updates),
        .version = static_cast<int64_t>(n)};
    ls.push_front(u);
    return db.upsert(
        std::move(root),
        std::move(ls),
        n,
        false /* compaction */,
        true /* write_to_fast */);
}

mpt::Nibbles proposal_prefix(bytes32_t const &block_id)
{
    return mpt::concat(PROPOSAL_NIBBLE, NibblesView{to_bytes(block_id)});
}

std::vector<bytes32_t>
get_proposal_block_ids(mpt::Db &db, uint64_t const block_number)
{
    static constexpr uint64_t PROPOSAL_PREFIX_LEN = 1 + sizeof(bytes32_t) * 2;

    class ProposalTraverseMachine final : public TraverseMachine
    {
        std::vector<bytes32_t> &block_ids_;
        Nibbles path_;

    public:
        explicit ProposalTraverseMachine(std::vector<bytes32_t> &block_ids)
            : block_ids_(block_ids)
        {
        }

        ProposalTraverseMachine(ProposalTraverseMachine const &other) = default;

        virtual bool down(unsigned char const branch, Node const &node) override
        {
            if (branch == INVALID_BRANCH) {
                MONAD_ASSERT(path_.nibble_size() == 0);
                path_ = node.path_nibble_view();
                return true;
            }

            Nibbles const new_path =
                concat(NibblesView{path_}, branch, node.path_nibble_view());
            if (node.has_value() && new_path.nibble_size() > 1) {
                if (new_path.nibble_size() < PROPOSAL_PREFIX_LEN) {
                    // Ignore proposals of old format that have a shorter prefix
                    // length
                    return false;
                }
                MONAD_ASSERT(new_path.nibble_size() == PROPOSAL_PREFIX_LEN);
                MONAD_ASSERT(new_path.get(0) == PROPOSAL_NIBBLE);
                auto const block_id_nibbles = new_path.substr(1);
                block_ids_.push_back(to_bytes32(block_id_nibbles));
                return false;
            }
            MONAD_ASSERT(new_path.nibble_size() < PROPOSAL_PREFIX_LEN);
            path_ = new_path;
            return true;
        }

        virtual void up(unsigned char const branch, Node const &node) override
        {
            auto const path_view = monad::mpt::NibblesView{path_};
            unsigned const prefix_size =
                branch == monad::mpt::INVALID_BRANCH
                    ? 0
                    : path_view.nibble_size() - node.path_nibbles_len() - 1;
            path_ = path_view.substr(0, prefix_size);
        }

        virtual bool
        should_visit(Node const &, unsigned char const branch) override
        {
            if (path_.nibble_size() == 0) {
                return branch == PROPOSAL_NIBBLE;
            }
            return true;
        }

        virtual std::unique_ptr<TraverseMachine> clone() const override
        {
            return std::make_unique<ProposalTraverseMachine>(*this);
        }
    };

    std::vector<bytes32_t> block_ids;
    ProposalTraverseMachine traverse(block_ids);
    db.traverse(db.load_root_for_version(block_number), traverse, block_number);
    return block_ids;
}

Result<std::vector<Transaction>> get_transactions(
    mpt::Db &db, uint64_t const block_number, bytes32_t const &block_id)
{
    Nibbles const prefix =
        block_id == bytes32_t{} ? finalized_nibbles : proposal_prefix(block_id);
    BOOST_OUTCOME_TRY(
        auto const cursor,
        db.find(concat(NibblesView{prefix}, TRANSACTION_NIBBLE), block_number));
    // traverse from cursor
    std::vector<Transaction> txs;
    txs.reserve(1000);
    GetAllMachine machine{
        [&txs](NibblesView const path, byte_string_view value) {
            // nibble size is even and first nibble starts at index 0
            MONAD_ASSERT(path.nibble_size() == path.data_size() * 2);
            // convert nibbles to byte_string
            byte_string_view raw{path.data(), path.data_size()};
            auto const index_res = rlp::decode_unsigned<uint32_t>(raw);
            MONAD_ASSERT(index_res.has_value());
            uint32_t const idx = index_res.value();
            auto tx_res = decode_transaction_db(value);
            MONAD_ASSERT(tx_res.has_value());
            auto &tx = tx_res.value().first;
            if (idx >= txs.size()) {
                txs.resize(idx + 1);
            }
            txs[idx] = std::move(tx);
        }};
    if (db.traverse(cursor, machine, block_number) == false) {
        MONAD_ASSERT(db.find({}, block_number).has_error());
        return DbError::version_no_longer_exist;
    }
    return txs;
}

bool for_each_code(
    mpt::Db &db, uint64_t const block,
    std::function<void(bytes32_t const &, byte_string_view)> const fn)
{
    class CodeTraverseMachine final : public TraverseMachine
    {
        std::function<void(bytes32_t const &, byte_string_view)> fn_;
        Nibbles path_;

    public:
        explicit CodeTraverseMachine(
            std::function<void(bytes32_t const &, byte_string_view)> const fn)
            : fn_(fn)
        {
        }

        CodeTraverseMachine(CodeTraverseMachine const &other) = default;

        virtual bool down(unsigned char const branch, Node const &node) override
        {
            if (branch == INVALID_BRANCH) {
                MONAD_ASSERT(path_.nibble_size() == 0);
                return true;
            }

            path_ = concat(NibblesView{path_}, branch, node.path_nibble_view());
            if (node.has_value()) {
                MONAD_ASSERT(path_.nibble_size() == (sizeof(bytes32_t) * 2));
                fn_(to_bytes({path_.data(), sizeof(bytes32_t)}), node.value());
                return false;
            }
            return true;
        }

        virtual void up(unsigned char const branch, Node const &node) override
        {
            auto const path_view = monad::mpt::NibblesView{path_};
            unsigned const prefix_size =
                branch == monad::mpt::INVALID_BRANCH
                    ? 0
                    : path_view.nibble_size() - node.path_nibbles_len() - 1;
            path_ = path_view.substr(0, prefix_size);
        }

        virtual std::unique_ptr<TraverseMachine> clone() const override
        {
            return std::make_unique<CodeTraverseMachine>(*this);
        }
    };

    auto const root = db.find(concat(FINALIZED_NIBBLE, CODE_NIBBLE), block);
    if (MONAD_UNLIKELY(!root.has_value())) {
        return false;
    }
    CodeTraverseMachine machine{fn};
    if (MONAD_UNLIKELY(!db.traverse(root.value(), machine, block))) {
        return false;
    }
    return true;
}

MONAD_NAMESPACE_END
