#include <monad/config.hpp>
#include <monad/core/account.hpp>
#include <monad/core/assert.h>
#include <monad/core/block.hpp>
#include <monad/core/byte_string.hpp>
#include <monad/core/bytes.hpp>
#include <monad/core/int.hpp>
#include <monad/core/likely.h>
#include <monad/core/receipt.hpp>
#include <monad/core/result.hpp>
#include <monad/core/rlp/account_rlp.hpp>
#include <monad/core/rlp/address_rlp.hpp>
#include <monad/core/rlp/block_rlp.hpp>
#include <monad/core/rlp/bytes_rlp.hpp>
#include <monad/core/rlp/int_rlp.hpp>
#include <monad/core/rlp/monad_block_rlp.hpp>
#include <monad/core/rlp/receipt_rlp.hpp>
#include <monad/core/rlp/transaction_rlp.hpp>
#include <monad/core/transaction.hpp>
#include <monad/core/unaligned.hpp>
#include <monad/db/util.hpp>
#include <monad/mpt/compute.hpp>
#include <monad/mpt/db.hpp>
#include <monad/mpt/nibbles_view.hpp>
#include <monad/mpt/node.hpp>
#include <monad/mpt/ondisk_db_config.hpp>
#include <monad/mpt/state_machine.hpp>
#include <monad/mpt/traverse.hpp>
#include <monad/mpt/update.hpp>
#include <monad/mpt/util.hpp>
#include <monad/rlp/decode.hpp>
#include <monad/rlp/decode_error.hpp>
#include <monad/rlp/encode2.hpp>

#include <boost/outcome/try.hpp>

#include <nlohmann/json_fwd.hpp>

#include <quill/Quill.h> // NOLINT
#include <quill/detail/LogMacros.h>

#include <algorithm>
#include <chrono>
#include <cstddef>
#include <cstdint>
#include <cstring>
#include <deque>
#include <filesystem>
#include <fstream>
#include <functional>
#include <istream>
#include <memory>
#include <optional>
#include <span>
#include <stdexcept>
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

    struct BinaryDbLoader
    {
    private:
        static constexpr uint64_t CHUNK_SIZE = 1ul << 13; // 8 kb

        ::monad::mpt::Db &db_;
        std::deque<mpt::Update> update_alloc_;
        std::deque<byte_string> bytes_alloc_;
        size_t buf_size_;
        std::unique_ptr<unsigned char[]> buf_;
        uint64_t block_id_;

    public:
        BinaryDbLoader(
            ::monad::mpt::Db &db, size_t buf_size, uint64_t const block_id)
            : db_{db}
            , buf_size_{buf_size}
            , buf_{std::make_unique_for_overwrite<unsigned char[]>(buf_size)}
            , block_id_{block_id}
        {
            MONAD_ASSERT(buf_size >= CHUNK_SIZE);
        };

        void load(std::istream &accounts, std::istream &code)
        {
            load(
                accounts,
                [&](byte_string_view in, UpdateList &updates) {
                    return parse_accounts(in, updates);
                },
                [&](UpdateList account_updates) {
                    UpdateList updates;
                    auto state_update = Update{
                        .key = state_nibbles,
                        .value = byte_string_view{},
                        .incarnation = false,
                        .next = std::move(account_updates),
                        .version = static_cast<int64_t>(block_id_)};
                    updates.push_front(state_update);

                    UpdateList finalized_updates;
                    Update finalized{
                        .key = finalized_nibbles,
                        .value = byte_string_view{},
                        .incarnation = false,
                        .next = std::move(updates),
                        .version = static_cast<int64_t>(block_id_),
                    };
                    finalized_updates.push_front(finalized);
                    db_.upsert(
                        std::move(finalized_updates), block_id_, false, false);
                    db_.update_finalized_version(block_id_);

                    update_alloc_.clear();
                    bytes_alloc_.clear();
                });
            load(
                code,
                [&](byte_string_view in, UpdateList &updates) {
                    return parse_code(in, updates);
                },
                [&](UpdateList code_updates) {
                    UpdateList updates;
                    auto code_update = Update{
                        .key = code_nibbles,
                        .value = byte_string_view{},
                        .incarnation = false,
                        .next = std::move(code_updates),
                        .version = static_cast<int64_t>(block_id_)};
                    updates.push_front(code_update);

                    UpdateList finalized_updates;
                    Update finalized{
                        .key = finalized_nibbles,
                        .value = byte_string_view{},
                        .incarnation = false,
                        .next = std::move(updates),
                        .version = static_cast<int64_t>(block_id_),
                    };
                    finalized_updates.push_front(finalized);
                    db_.upsert(
                        std::move(finalized_updates), block_id_, false, false);

                    update_alloc_.clear();
                    bytes_alloc_.clear();
                });
        }

    private:
        static constexpr auto storage_entry_size = sizeof(bytes32_t) * 2;
        static_assert(storage_entry_size == 64);

        void load(
            std::istream &input,
            std::function<size_t(byte_string_view, UpdateList &)> fparse,
            std::function<void(UpdateList)> fwrite)
        {
            UpdateList updates;
            size_t total_processed = 0;
            size_t total_read = 0;
            while (input.read((char *)buf_.get() + total_read, CHUNK_SIZE)) {
                auto const count = static_cast<size_t>(input.gcount());
                MONAD_ASSERT(count <= CHUNK_SIZE);
                total_read += count;
                total_processed += fparse(
                    byte_string_view{
                        buf_.get() + total_processed,
                        total_read - total_processed},
                    updates);
                if (MONAD_UNLIKELY((total_read + CHUNK_SIZE) > buf_size_)) {
                    fwrite(std::move(updates));
                    std::memmove(
                        buf_.get(),
                        buf_.get() + total_processed,
                        total_read - total_processed);
                    total_read -= total_processed;
                    total_processed = 0;
                    updates.clear();
                }
            }

            auto const count = static_cast<size_t>(input.gcount());
            MONAD_ASSERT(count <= CHUNK_SIZE);
            total_read += count;
            total_processed += fparse(
                byte_string_view{
                    buf_.get() + total_processed, total_read - total_processed},
                updates);
            MONAD_ASSERT(total_processed == total_read);
            MONAD_ASSERT(input.eof());

            fwrite(std::move(updates));
        }

        size_t parse_accounts(byte_string_view in, UpdateList &account_updates)
        {
            constexpr auto account_fixed_size =
                sizeof(bytes32_t) + sizeof(uint256_t) + sizeof(uint64_t) +
                sizeof(bytes32_t) + sizeof(uint64_t);
            static_assert(account_fixed_size == 112);
            size_t total_processed = 0;
            while (in.size() >= account_fixed_size) {
                constexpr auto num_storage_offset =
                    account_fixed_size - sizeof(uint64_t);
                auto const num_storage = unaligned_load<uint64_t>(
                    in.substr(num_storage_offset, sizeof(uint64_t)).data());
                auto const storage_size = num_storage * storage_entry_size;
                auto const entry_size = account_fixed_size + storage_size;
                MONAD_ASSERT(entry_size <= buf_size_);
                if (in.size() < entry_size) {
                    return total_processed;
                }
                auto &update = update_alloc_.emplace_back(handle_account(in));
                if (num_storage) {
                    update.next = handle_storage(
                        in.substr(account_fixed_size, storage_size));
                }
                account_updates.push_front(update);
                total_processed += entry_size;
                in = in.substr(entry_size);
            }
            return total_processed;
        }

        size_t parse_code(byte_string_view in, UpdateList &code_updates)
        {
            constexpr auto hash_and_len_size =
                sizeof(bytes32_t) + sizeof(uint64_t);
            static_assert(hash_and_len_size == 40);
            size_t total_processed = 0;
            while (in.size() >= hash_and_len_size) {
                auto const code_len = unaligned_load<uint64_t>(
                    in.substr(sizeof(bytes32_t), sizeof(uint64_t)).data());
                auto const entry_size = code_len + hash_and_len_size;
                MONAD_ASSERT(entry_size <= buf_size_);
                if (in.size() < entry_size) {
                    return total_processed;
                }
                code_updates.push_front(update_alloc_.emplace_back(Update{
                    .key = in.substr(0, sizeof(bytes32_t)),
                    .value = in.substr(hash_and_len_size, code_len),
                    .incarnation = false,
                    .next = UpdateList{},
                    .version = static_cast<int64_t>(block_id_)}));

                total_processed += entry_size;
                in = in.substr(entry_size);
            }
            return total_processed;
        }

        Update handle_account(byte_string_view curr)
        {
            constexpr auto balance_offset = sizeof(bytes32_t);
            constexpr auto nonce_offset = balance_offset + sizeof(uint256_t);
            constexpr auto code_hash_offset = nonce_offset + sizeof(uint64_t);

            return Update{
                .key = curr.substr(0, sizeof(bytes32_t)),
                .value = bytes_alloc_.emplace_back(encode_account_db(
                    Address{}, // TODO: Update this when binary checkpoint
                               // includes unhashed address
                    Account{
                        .balance = unaligned_load<uint256_t>(
                            curr.substr(balance_offset, sizeof(uint256_t))
                                .data()),
                        .code_hash = unaligned_load<bytes32_t>(
                            curr.substr(code_hash_offset, sizeof(bytes32_t))
                                .data()),
                        .nonce = unaligned_load<uint64_t>(
                            curr.substr(nonce_offset, sizeof(uint64_t))
                                .data())})),
                .incarnation = false,
                .next = UpdateList{},
                .version = static_cast<int64_t>(block_id_)};
        }

        UpdateList handle_storage(byte_string_view in)
        {
            UpdateList storage_updates;
            while (!in.empty()) {
                storage_updates.push_front(update_alloc_.emplace_back(Update{
                    .key = in.substr(0, sizeof(bytes32_t)),
                    .value = bytes_alloc_.emplace_back(encode_storage_db(
                        bytes32_t{}, // TODO: update this when binary checkpoint
                                     // includes unhashed storage slot
                        unaligned_load<bytes32_t>(
                            in.substr(sizeof(bytes32_t), sizeof(bytes32_t))
                                .data()))),
                    .incarnation = false,
                    .next = UpdateList{},
                    .version = static_cast<int64_t>(block_id_)}));
                in = in.substr(storage_entry_size);
            }
            return storage_updates;
        }
    };

    struct ComputeAccountLeaf
    {
        static byte_string compute(Node const &node)
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
                std::copy_n(
                    node.data().data(), sizeof(bytes32_t), storage_root.bytes);
            }
            return rlp::encode_account(acct.value(), storage_root);
        }
    };

    struct ComputeStorageLeaf
    {
        static byte_string compute(Node const &node)
        {
            MONAD_ASSERT(node.has_value());
            auto encoded_storage = node.value();
            auto const storage = decode_storage_db_ignore_slot(encoded_storage);
            MONAD_ASSERT(!storage.has_error());
            return rlp::encode_string2(storage.value());
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
        static byte_string_view process(byte_string_view enc)
        {
            auto const enc_receipt =
                parse_encoded_receipt_ignore_log_index(enc);
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

    struct TransactionLeafProcess
    {
        static byte_string_view process(byte_string_view enc)
        {
            auto const enc_transaction =
                parse_encoded_transaction_ignore_sender(enc);
            MONAD_ASSERT(!enc_transaction.has_error());
            return enc_transaction.value();
        }
    };

    using AccountMerkleCompute = MerkleComputeBase<ComputeAccountLeaf>;
    using StorageMerkleCompute = MerkleComputeBase<ComputeStorageLeaf>;

    struct StorageRootMerkleCompute : public StorageMerkleCompute
    {
        virtual unsigned
        compute(unsigned char *const buffer, Node *const node) override
        {
            MONAD_ASSERT(node->has_value());
            return encode_two_pieces(
                buffer,
                node->path_nibble_view(),
                ComputeAccountLeaf::compute(*node),
                true);
        }
    };

    struct AccountRootMerkleCompute : public AccountMerkleCompute
    {
        virtual unsigned compute(unsigned char *const, Node *const) override
        {
            return 0;
        }
    };

    struct EmptyCompute final : Compute
    {
        virtual unsigned compute_len(
            std::span<ChildData>, uint16_t, NibblesView,
            std::optional<byte_string_view>) override
        {
            return 0;
        }

        virtual unsigned compute_branch(unsigned char *, Node *) override
        {
            return 0;
        }

        virtual unsigned compute(unsigned char *, Node *) override
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
    static StorageMerkleCompute storage_compute;
    static StorageRootMerkleCompute storage_root_compute;

    static VarLenMerkleCompute generic_merkle_compute;
    static RootVarLenMerkleCompute generic_root_merkle_compute;

    static VarLenMerkleCompute<ReceiptLeafProcessor> receipt_compute;
    static RootVarLenMerkleCompute<ReceiptLeafProcessor> receipt_root_compute;
    static VarLenMerkleCompute<TransactionLeafProcess> transaction_compute;
    static RootVarLenMerkleCompute<TransactionLeafProcess>
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
            return storage_root_compute;
        }
        else {
            return storage_compute;
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
    MONAD_ASSERT(
        (nibble == STATE_NIBBLE || nibble == CODE_NIBBLE ||
         nibble == RECEIPT_NIBBLE || nibble == CALL_FRAME_NIBBLE ||
         nibble == TRANSACTION_NIBBLE || nibble == BLOCKHEADER_NIBBLE ||
         nibble == WITHDRAWAL_NIBBLE || nibble == OMMER_NIBBLE ||
         nibble == TX_HASH_NIBBLE || nibble == BLOCK_HASH_NIBBLE ||
         nibble == BFT_BLOCK_NIBBLE) ||
        depth != prefix_length);
    if (MONAD_UNLIKELY(depth == prefix_length)) {
        MONAD_ASSERT(table == TableType::Prefix);
        if (nibble == STATE_NIBBLE) {
            table = TableType::State;
        }
        else if (nibble == RECEIPT_NIBBLE) {
            table = TableType::Receipt;
        }
        else if (nibble == TRANSACTION_NIBBLE) {
            table = TableType::Transaction;
        }
        else if (nibble == CODE_NIBBLE) {
            table = TableType::Code;
        }
        else if (nibble == WITHDRAWAL_NIBBLE) {
            table = TableType::Withdrawal;
        }
        else if (nibble == TX_HASH_NIBBLE) {
            table = TableType::TxHash;
        }
        else if (nibble == BLOCK_HASH_NIBBLE) {
            table = TableType::BlockHash;
        }
        else {
            // No subtrie in the rest tables, thus treated the same as
            // Table::Prefix
            MONAD_ASSERT(
                nibble == BLOCKHEADER_NIBBLE || nibble == BFT_BLOCK_NIBBLE ||
                nibble == OMMER_NIBBLE || nibble == CALL_FRAME_NIBBLE);
        }
    }
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

Result<std::pair<byte_string_view, byte_string_view>>
decode_storage_db_raw(byte_string_view &enc)
{
    BOOST_OUTCOME_TRY(auto payload, rlp::parse_list_metadata(enc));
    BOOST_OUTCOME_TRY(byte_string_view const slot, rlp::decode_string(payload));
    BOOST_OUTCOME_TRY(byte_string_view const val, rlp::decode_string(payload));
    return {slot, val};
}

Result<std::pair<bytes32_t, bytes32_t>> decode_storage_db(byte_string_view &enc)
{
    BOOST_OUTCOME_TRY(auto res, decode_storage_db_raw(enc));
    if (!enc.empty()) {
        return rlp::DecodeError::InputTooLong;
    }
    return {to_bytes(res.first), to_bytes(res.second)};
}

Result<byte_string_view> decode_storage_db_ignore_slot(byte_string_view &enc)
{
    BOOST_OUTCOME_TRY(auto const res, decode_storage_db_raw(enc));
    if (!enc.empty()) {
        return rlp::DecodeError::InputTooLong;
    }
    return res.second;
};

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

void load_from_binary(
    mpt::Db &db, std::istream &accounts, std::istream &code,
    uint64_t const init_block_number, size_t const buf_size)
{
    if (db.root().is_valid()) {
        throw std::runtime_error(
            "Unable to load snapshot to an existing db, truncate the "
            "existing db to empty and try again");
    }
    BinaryDbLoader loader{
        db, buf_size, db.is_on_disk() ? init_block_number : 0};
    loader.load(accounts, code);
}

void load_header(mpt::Db &db, BlockHeader const &header)
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
    db.upsert(
        std::move(ls), n, false /* compaction */, true /* write_to_fast */);
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

        virtual bool should_visit(Node const &, unsigned char branch) override
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

std::optional<BlockHeader> read_eth_header(
    mpt::Db const &db, uint64_t const block, mpt::NibblesView prefix)
{
    auto const query_res =
        db.get(mpt::concat(prefix, BLOCKHEADER_NIBBLE), block);
    if (MONAD_UNLIKELY(!query_res.has_value())) {
        return std::nullopt;
    }
    byte_string_view view{query_res.value()};
    auto const decoded = rlp::decode_block_header(view);
    MONAD_ASSERT(decoded.has_value());
    return decoded.value();
}

std::optional<byte_string> query_consensus_header(
    mpt::Db const &db, uint64_t const block, mpt::NibblesView const prefix)
{
    auto const query_res = db.get(mpt::concat(prefix, BFT_BLOCK_NIBBLE), block);
    if (MONAD_UNLIKELY(!query_res.has_value())) {
        return std::nullopt;
    }
    return byte_string{query_res.value()};
}

std::optional<MonadConsensusBlockHeader> read_consensus_header(
    mpt::Db const &db, uint64_t const block, mpt::NibblesView const prefix)
{
    return query_consensus_header(db, block, prefix)
        .transform([](byte_string const &data) {
            byte_string_view view{data};
            auto const decoded = rlp::decode_consensus_block_header(view);
            MONAD_ASSERT(decoded.has_value());
            return decoded.value();
        });
}

MONAD_NAMESPACE_END
