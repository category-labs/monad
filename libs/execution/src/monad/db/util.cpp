#include <monad/config.hpp>
#include <monad/core/account.hpp>
#include <monad/core/assert.h>
#include <monad/core/byte_string.hpp>
#include <monad/core/bytes.hpp>
#include <monad/core/int.hpp>
#include <monad/core/likely.h>
#include <monad/core/result.hpp>
#include <monad/core/rlp/account_rlp.hpp>
#include <monad/core/rlp/address_rlp.hpp>
#include <monad/core/rlp/bytes_rlp.hpp>
#include <monad/core/rlp/int_rlp.hpp>
#include <monad/core/unaligned.hpp>
#include <monad/db/util.hpp>
#include <monad/mpt/compute.hpp>
#include <monad/mpt/db.hpp>
#include <monad/mpt/nibbles_view.hpp>
#include <monad/mpt/node.hpp>
#include <monad/mpt/ondisk_db_config.hpp>
#include <monad/mpt/state_machine.hpp>
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
#include <fcntl.h>
#include <filesystem>
#include <fstream>
#include <functional>
#include <istream>
#include <memory>
#include <optional>
#include <span>
#include <stdexcept>
#include <string>
#include <sys/mman.h>
#include <sys/stat.h>
#include <unistd.h>
#include <utility>

MONAD_NAMESPACE_BEGIN

using namespace monad::mpt;

namespace
{
    struct BinaryDbLoader
    {
    private:
        ::monad::mpt::Db &db_;
        std::deque<mpt::Update> update_alloc_;
        std::deque<byte_string> bytes_alloc_;
        uint64_t block_id_;
        size_t buf_size_;

    public:
        BinaryDbLoader(
            ::monad::mpt::Db &db, uint64_t const block_id, size_t buf_size)
            : db_{db}
            , block_id_{block_id}
            , buf_size_{buf_size}
        {
        }

        void load(int account_fd, int code_fd)
        {
            MONAD_DEBUG_ASSERT(account_fd != -1 && code_fd != -1);
            load(account_fd, [this](uint8_t const *content, size_t const size) {
                parse_account(content, size);
            });
            load(code_fd, [this](uint8_t const *content, size_t const size) {
                parse_code(content, size);
            });
        }

    private:
        static constexpr auto storage_entry_size = sizeof(bytes32_t) * 2;
        static_assert(storage_entry_size == 64);
        static constexpr auto account_fixed_size =
            sizeof(bytes32_t) + sizeof(uint256_t) + sizeof(uint64_t) +
            sizeof(bytes32_t) + sizeof(uint64_t);
        static_assert(account_fixed_size == 112);
        static constexpr auto num_storage_offset =
            account_fixed_size - sizeof(uint64_t);
        static constexpr auto balance_offset = sizeof(bytes32_t);
        static constexpr auto nonce_offset = balance_offset + sizeof(uint256_t);
        static constexpr auto code_hash_offset =
            nonce_offset + sizeof(uint64_t);

        static constexpr auto hash_and_len_size =
            sizeof(bytes32_t) + sizeof(uint64_t);
        static_assert(hash_and_len_size == 40);

        void
        load(int fd, std::function<void(uint8_t const *, size_t const)> fparse)
        {
            struct stat file_stat;
            MONAD_ASSERT(fstat(fd, &file_stat) != -1);
            size_t file_size = static_cast<size_t>(file_stat.st_size);
            void *mmaped_content =
                mmap(nullptr, file_size, PROT_READ, MAP_SHARED, fd, 0);
            MONAD_ASSERT(mmaped_content != MAP_FAILED);
            fparse(reinterpret_cast<uint8_t *>(mmaped_content), file_size);
            MONAD_ASSERT(munmap(mmaped_content, file_size) != -1);
            MONAD_ASSERT(close(fd) != -1);
        }

        void parse_account(uint8_t const *content, size_t const size)
        {
            size_t total_processed = 0;
            size_t current_processed = 0;
            UpdateList account_updates{};
            while (total_processed < size) {
                // read account
                byte_string_view account{
                    content + total_processed, account_fixed_size};
                auto &update =
                    update_alloc_.emplace_back(handle_account(account));
                total_processed += account_fixed_size;
                current_processed += account_fixed_size;

                // read storage
                auto const num_storage = unaligned_load<uint64_t>(
                    account.substr(num_storage_offset, sizeof(uint64_t))
                        .data());
                if (num_storage) {
                    byte_string_view storage{
                        content + total_processed,
                        num_storage * storage_entry_size};
                    update.next = handle_storage(storage);
                    total_processed += num_storage * storage_entry_size;
                    current_processed += account_fixed_size;
                }
                account_updates.push_front(update);

                if (current_processed > buf_size_) {
                    write_updates(std::move(account_updates), true);
                    current_processed = 0;
                    account_updates.clear();
                }
            }

            MONAD_ASSERT(total_processed == size);
            write_updates(std::move(account_updates), true);
            account_updates.clear();
        }

        void parse_code(uint8_t const *content, size_t const size)
        {
            size_t total_processed = 0;
            size_t current_processed = 0;
            UpdateList code_updates{};
            while (total_processed < size) {
                byte_string_view code_hash_and_len{
                    content + total_processed, hash_and_len_size};
                auto const code_len = unaligned_load<uint64_t>(
                    code_hash_and_len
                        .substr(sizeof(bytes32_t), sizeof(uint64_t))
                        .data());
                total_processed += hash_and_len_size;
                current_processed += hash_and_len_size;

                byte_string_view code{content + total_processed, code_len};
                code_updates.push_front(update_alloc_.emplace_back(Update{
                    .key = code_hash_and_len.substr(0, sizeof(bytes32_t)),
                    .value = code,
                    .incarnation = false,
                    .next = UpdateList{},
                    .version = static_cast<int64_t>(block_id_)}));

                total_processed += code_len;
                current_processed += code_len;

                if (current_processed > buf_size_) {
                    write_updates(std::move(code_updates), false);
                    current_processed = 0;
                    code_updates.clear();
                }
            }

            MONAD_ASSERT(total_processed == size);
            write_updates(std::move(code_updates), false);
            code_updates.clear();
        }

        void write_updates(UpdateList &&update_list, bool const is_account)
        {
            UpdateList updates;
            auto update = Update{
                .key = is_account ? state_nibbles : code_nibbles,
                .value = byte_string_view{},
                .incarnation = false,
                .next = std::move(update_list),
                .version = static_cast<int64_t>(block_id_)};
            updates.push_front(update);

            db_.upsert(std::move(updates), block_id_, false, false);

            update_alloc_.clear();
            bytes_alloc_.clear();
        }

        Update handle_account(byte_string_view curr)
        {
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

mpt::Compute &MachineBase::get_compute() const
{
    static EmptyCompute empty_compute;

    static AccountMerkleCompute account_compute;
    static AccountRootMerkleCompute account_root_compute;
    static StorageMerkleCompute storage_compute;
    static StorageRootMerkleCompute storage_root_compute;

    static VarLenMerkleCompute generic_merkle_compute;
    static RootVarLenMerkleCompute generic_root_merkle_compute;

    if (MONAD_LIKELY(trie_section == TrieType::State)) {
        MONAD_ASSERT(depth >= PREFIX_LEN);
        if (MONAD_UNLIKELY(depth == PREFIX_LEN)) {
            return account_root_compute;
        }
        else if (depth < PREFIX_LEN + 2 * sizeof(bytes32_t)) {
            return account_compute;
        }
        else if (depth == PREFIX_LEN + 2 * sizeof(bytes32_t)) {
            return storage_root_compute;
        }
        else {
            return storage_compute;
        }
    }
    else if (
        trie_section == TrieType::Receipt ||
        trie_section == TrieType::Transaction) {
        return depth == PREFIX_LEN ? generic_root_merkle_compute
                                   : generic_merkle_compute;
    }
    else {
        return empty_compute;
    }
}

void MachineBase::down(unsigned char const nibble)
{
    ++depth;
    MONAD_ASSERT(depth <= MAX_DEPTH);
    MONAD_ASSERT(
        (nibble == STATE_NIBBLE || nibble == CODE_NIBBLE ||
         nibble == RECEIPT_NIBBLE || nibble == TRANSACTION_NIBBLE) ||
        depth != PREFIX_LEN);
    if (MONAD_UNLIKELY(depth == PREFIX_LEN)) {
        MONAD_ASSERT(trie_section == TrieType::Prefix);
        if (nibble == STATE_NIBBLE) {
            trie_section = TrieType::State;
        }
        else if (nibble == RECEIPT_NIBBLE) {
            trie_section = TrieType::Receipt;
        }
        else if (nibble == TRANSACTION_NIBBLE) {
            trie_section = TrieType::Transaction;
        }
        else {
            trie_section = TrieType::Code;
        }
    }
}

void MachineBase::up(size_t const n)
{
    MONAD_ASSERT(n <= depth);
    depth -= static_cast<uint8_t>(n);
    if (MONAD_UNLIKELY(depth < PREFIX_LEN)) {
        trie_section = TrieType::Prefix;
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
    constexpr uint64_t CACHE_DEPTH = PREFIX_LEN + 5;
    return depth <= CACHE_DEPTH &&
           (trie_section == TrieType::State || trie_section == TrieType::Code);
}

bool OnDiskMachine::compact() const
{
    return true;
}

std::unique_ptr<StateMachine> OnDiskMachine::clone() const
{
    return std::make_unique<OnDiskMachine>(*this);
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

Result<std::pair<Address, Account>> decode_account_db(byte_string_view &enc)
{
    BOOST_OUTCOME_TRY(auto payload, rlp::parse_list_metadata(enc));
    BOOST_OUTCOME_TRY(auto const address, rlp::decode_address(payload));
    BOOST_OUTCOME_TRY(auto const acct, decode_account_db_helper(payload));
    return {address, acct};
}

Result<Account> decode_account_db_ignore_address(byte_string_view &enc)
{
    BOOST_OUTCOME_TRY(auto payload, rlp::parse_list_metadata(enc));
    BOOST_OUTCOME_TRY(
        auto const address_byte_view, rlp::parse_string_metadata(payload));
    if (MONAD_UNLIKELY(address_byte_view.size() != sizeof(Address))) {
        return rlp::DecodeError::ArrayLengthUnexpected;
    }
    return decode_account_db_helper(payload);
}

byte_string encode_storage_db(bytes32_t const &key, bytes32_t const &val)
{
    byte_string encoded_storage;
    encoded_storage += rlp::encode_bytes32_compact(key);
    encoded_storage += rlp::encode_bytes32_compact(val);
    return rlp::encode_list2(encoded_storage);
}

Result<std::pair<bytes32_t, bytes32_t>> decode_storage_db(byte_string_view &enc)
{
    BOOST_OUTCOME_TRY(auto payload, rlp::parse_list_metadata(enc));

    std::pair<bytes32_t, bytes32_t> storage;
    BOOST_OUTCOME_TRY(storage.first, rlp::decode_bytes32_compact(payload));
    BOOST_OUTCOME_TRY(storage.second, rlp::decode_bytes32_compact(payload));

    if (MONAD_UNLIKELY(!payload.empty())) {
        return rlp::DecodeError::InputTooLong;
    }

    return storage;
}

Result<byte_string_view> decode_storage_db_ignore_slot(byte_string_view &enc)
{
    BOOST_OUTCOME_TRY(auto payload, rlp::parse_list_metadata(enc));

    BOOST_OUTCOME_TRY(rlp::decode_bytes32_compact(payload));
    BOOST_OUTCOME_TRY(auto const output, rlp::decode_string(payload));

    if (MONAD_UNLIKELY(!payload.empty())) {
        return rlp::DecodeError::InputTooLong;
    }

    return output;
};

void write_to_file(
    nlohmann::json const &j, std::filesystem::path const &root_path,
    uint64_t const block_number)
{
    auto const start_time = std::chrono::steady_clock::now();

    auto const dir = root_path / std::to_string(block_number);
    std::filesystem::create_directory(dir);
    MONAD_ASSERT(std::filesystem::is_directory(dir));

    auto const file = dir / "state.json";
    MONAD_ASSERT(!std::filesystem::exists(file));
    std::ofstream ofile(file);
    ofile << j.dump(4);

    auto const finished_time = std::chrono::steady_clock::now();
    auto const elapsed_ms =
        std::chrono::duration_cast<std::chrono::milliseconds>(
            finished_time - start_time);
    LOG_INFO(
        "Finished dumping to json file at block = {}, time elapsed = {}",
        block_number,
        elapsed_ms);
}

void load_from_binary(
    mpt::Db &db, int account_fd, int code_fd, uint64_t const init_block_number,
    size_t const buf_size)
{
    if (db.root().is_valid()) {
        throw std::runtime_error(
            "Unable to load snapshot to an existing db, truncate the "
            "existing db to empty and try again");
    }
    BinaryDbLoader loader{
        db, db.is_on_disk() ? init_block_number : 0, buf_size};
    loader.load(account_fd, code_fd);
}

MONAD_NAMESPACE_END
