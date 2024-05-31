#include <monad/config.hpp>
#include <monad/core/account.hpp>
#include <monad/core/address.hpp>
#include <monad/core/assert.h>
#include <monad/core/byte_string.hpp>
#include <monad/core/bytes.hpp>
#include <monad/core/fmt/bytes_fmt.hpp> // NOLINT
#include <monad/core/fmt/int_fmt.hpp> // NOLINT
#include <monad/core/int.hpp>
#include <monad/core/keccak.hpp>
#include <monad/core/likely.h>
#include <monad/core/receipt.hpp>
#include <monad/core/result.hpp>
#include <monad/core/rlp/account_rlp.hpp>
#include <monad/core/rlp/bytes_rlp.hpp>
#include <monad/core/rlp/int_rlp.hpp>
#include <monad/core/rlp/receipt_rlp.hpp>
#include <monad/core/unaligned.hpp>
#include <monad/db/trie_db.hpp>
#include <monad/execution/code_analysis.hpp>
#include <monad/mpt/compute.hpp>
#include <monad/mpt/db.hpp>
#include <monad/mpt/nibbles_view.hpp>
#include <monad/mpt/nibbles_view_fmt.hpp> // NOLINT
#include <monad/mpt/node.hpp>
#include <monad/mpt/ondisk_db_config.hpp>
#include <monad/mpt/state_machine.hpp>
#include <monad/mpt/traverse.hpp>
#include <monad/mpt/update.hpp>
#include <monad/mpt/util.hpp>
#include <monad/rlp/decode.hpp>
#include <monad/rlp/decode_error.hpp>
#include <monad/rlp/encode2.hpp>
#include <monad/state2/state_deltas.hpp>

#include <boost/outcome/try.hpp>

#include <ethash/hash_types.hpp>

#include <evmc/evmc.hpp>
#include <evmc/hex.hpp>

#include <nlohmann/json.hpp>
#include <nlohmann/json_fwd.hpp>

#include <quill/bundled/fmt/core.h>
#include <quill/bundled/fmt/format.h>

#include <algorithm>
#include <concepts>
#include <cstdint>
#include <cstdlib>
#include <cstring>
#include <deque>
#include <functional>
#include <istream>
#include <memory>
#include <optional>
#include <span>
#include <stdexcept>
#include <utility>
#include <vector>

MONAD_NAMESPACE_BEGIN

using namespace monad::mpt;

namespace
{
    constexpr unsigned char state_nibble = 0;
    constexpr unsigned char code_nibble = 1;
    constexpr unsigned char receipt_nibble = 2;
    auto const state_nibbles = concat(state_nibble);
    auto const code_nibbles = concat(code_nibble);
    auto const receipt_nibbles = concat(receipt_nibble);

    template <class T>
        requires std::same_as<T, bytes32_t> || std::same_as<T, Address>
    constexpr byte_string to_key(T const &arg)
    {
        auto const h = keccak256(arg.bytes, sizeof(arg.bytes));
        return byte_string{h.bytes, sizeof(ethash::hash256)};
    }

    byte_string encode_account_db(Account const &account)
    {
        byte_string encoded_account;
        encoded_account += rlp::encode_unsigned(account.incarnation.to_int());
        encoded_account += rlp::encode_unsigned(account.nonce);
        encoded_account += rlp::encode_unsigned(account.balance);
        if (account.code_hash != NULL_HASH) {
            encoded_account += rlp::encode_bytes32(account.code_hash);
        }
        return rlp::encode_list2(encoded_account);
    }

    Result<Account> decode_account_db(byte_string_view &enc)
    {
        BOOST_OUTCOME_TRY(auto payload, rlp::parse_list_metadata(enc));

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
            auto const acct = decode_account_db(encoded_account);
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
            MONAD_ASSERT(node.value().front());
            MONAD_ASSERT(node.value().size() <= sizeof(bytes32_t));

            return rlp::encode_string2(node.value());
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

    struct BinaryDbLoader
    {
    private:
        static constexpr auto chunk_size = 1ul << 13; // 8 kb

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
            MONAD_ASSERT(buf_size >= chunk_size);
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
                        .next = std::move(account_updates)};
                    updates.push_front(state_update);

                    db_.upsert(std::move(updates), block_id_, false, false);

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
                        .next = std::move(code_updates)};
                    updates.push_front(code_update);

                    db_.upsert(std::move(updates), block_id_, false, false);

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
            while (input.read((char *)buf_.get() + total_read, chunk_size)) {
                auto const count = static_cast<size_t>(input.gcount());
                MONAD_ASSERT(count <= chunk_size);
                total_read += count;
                total_processed += fparse(
                    byte_string_view{
                        buf_.get() + total_processed,
                        total_read - total_processed},
                    updates);
                if (MONAD_UNLIKELY((total_read + chunk_size) > buf_size_)) {
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
            MONAD_ASSERT(count <= chunk_size);
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
                    .next = UpdateList{}}));

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
                .value = bytes_alloc_.emplace_back(encode_account_db(Account{
                    .balance = unaligned_load<uint256_t>(
                        curr.substr(balance_offset, sizeof(uint256_t)).data()),
                    .code_hash = unaligned_load<bytes32_t>(
                        curr.substr(code_hash_offset, sizeof(bytes32_t))
                            .data()),
                    .nonce = unaligned_load<uint64_t>(
                        curr.substr(nonce_offset, sizeof(uint64_t)).data())})),
                .incarnation = false,
                .next = UpdateList{}};
        }

        UpdateList handle_storage(byte_string_view in)
        {
            UpdateList storage_updates;
            while (!in.empty()) {
                storage_updates.push_front(update_alloc_.emplace_back(Update{
                    .key = in.substr(0, sizeof(bytes32_t)),
                    .value = rlp::zeroless_view(
                        in.substr(sizeof(bytes32_t), sizeof(bytes32_t))),
                    .incarnation = false,
                    .next = UpdateList{}}));
                in = in.substr(storage_entry_size);
            }
            return storage_updates;
        }
    };
}

struct TrieDb::Machine : public mpt::StateMachine
{
    enum class TrieType : uint8_t
    {
        Prefix,
        State,
        Code,
        Receipt
    };

    uint8_t depth{0};
    TrieType trie_section{TrieType::Prefix};
    static constexpr auto prefix_len = 1;
    static constexpr auto max_depth = mpt::BLOCK_NUM_NIBBLES_LEN + prefix_len +
                                      sizeof(bytes32_t) * 2 +
                                      sizeof(bytes32_t) * 2;

    virtual mpt::Compute &get_compute() const override
    {
        static EmptyCompute empty_compute;

        static AccountMerkleCompute account_compute;
        static AccountRootMerkleCompute account_root_compute;
        static StorageMerkleCompute storage_compute;
        static StorageRootMerkleCompute storage_root_compute;

        static VarLenMerkleCompute receipt_compute;
        static RootVarLenMerkleCompute receipt_root_compute;

        if (MONAD_LIKELY(trie_section == TrieType::State)) {
            MONAD_ASSERT(depth >= BLOCK_NUM_NIBBLES_LEN + prefix_len);
            if (MONAD_UNLIKELY(depth == BLOCK_NUM_NIBBLES_LEN + prefix_len)) {
                return account_root_compute;
            }
            else if (
                depth <
                BLOCK_NUM_NIBBLES_LEN + prefix_len + 2 * sizeof(bytes32_t)) {
                return account_compute;
            }
            else if (
                depth ==
                BLOCK_NUM_NIBBLES_LEN + prefix_len + 2 * sizeof(bytes32_t)) {
                return storage_root_compute;
            }
            else {
                return storage_compute;
            }
        }
        else if (trie_section == TrieType::Receipt) {
            return depth == prefix_len + BLOCK_NUM_NIBBLES_LEN
                       ? receipt_root_compute
                       : receipt_compute;
        }
        else {
            return empty_compute;
        }
    }

    virtual void down(unsigned char const nibble) override
    {
        ++depth;
        MONAD_ASSERT(depth <= max_depth);
        MONAD_ASSERT(
            (nibble == state_nibble || nibble == code_nibble ||
             nibble == receipt_nibble) ||
            depth != prefix_len + BLOCK_NUM_NIBBLES_LEN);
        if (MONAD_UNLIKELY(depth == prefix_len + BLOCK_NUM_NIBBLES_LEN)) {
            MONAD_ASSERT(trie_section == TrieType::Prefix);
            if (nibble == state_nibble) {
                trie_section = TrieType::State;
            }
            else if (nibble == receipt_nibble) {
                trie_section = TrieType::Receipt;
            }
            else {
                trie_section = TrieType::Code;
            }
        }
    }

    virtual void up(size_t const n) override
    {
        MONAD_ASSERT(n <= depth);
        depth -= static_cast<uint8_t>(n);
        if (MONAD_UNLIKELY(depth < prefix_len + BLOCK_NUM_NIBBLES_LEN)) {
            trie_section = TrieType::Prefix;
        }
    }
};

struct TrieDb::InMemoryMachine final : public TrieDb::Machine
{
    virtual bool cache() const override
    {
        return true;
    }

    virtual bool compact() const override
    {
        return false;
    }

    virtual std::unique_ptr<StateMachine> clone() const override
    {
        return std::make_unique<InMemoryMachine>(*this);
    }
};

struct TrieDb::OnDiskMachine final : public TrieDb::Machine
{
    static constexpr auto cache_depth =
        mpt::BLOCK_NUM_NIBBLES_LEN + prefix_len + 5;

    virtual bool cache() const override
    {
        return depth <= cache_depth && trie_section != TrieType::Receipt;
    }

    virtual bool compact() const override
    {
        return depth >= BLOCK_NUM_NIBBLES_LEN;
    }

    virtual std::unique_ptr<StateMachine> clone() const override
    {
        return std::make_unique<OnDiskMachine>(*this);
    }
};

enum class TrieDb::Mode
{
    InMemory,
    OnDisk,
    OnDiskReadOnly
};

TrieDb::TrieDb(mpt::ReadOnlyOnDiskDbConfig const &config)
    : db_{config}
    , block_number_{db_.get_latest_block_id().value()}
    , mode_{Mode::OnDiskReadOnly}
{
}

TrieDb::TrieDb(std::optional<mpt::OnDiskDbConfig> const &config)
    : machine_{[&] -> std::unique_ptr<Machine> {
        if (config.has_value()) {
            return std::make_unique<OnDiskMachine>();
        }
        return std::make_unique<InMemoryMachine>();
    }()}
    , db_{config.has_value() ? mpt::Db{*machine_, config.value()}
                             : mpt::Db{*machine_}}
    , block_number_{[&] {
        if (config.has_value()) {
            if (config->start_block_id.has_value()) {
                // throw error on invalid block number in config
                if (!db_.get_latest_block_id().has_value() ||
                    !db_.get_earliest_block_id().has_value()) {
                    throw std::runtime_error(
                        "No valid history in existing db to resume from");
                }
                if (config->start_block_id >
                        db_.get_latest_block_id().value() ||
                    config->start_block_id <
                        db_.get_earliest_block_id().value()) {
                    throw std::runtime_error(fmt::format(
                        "Invalid starting block id to resume, the valid block "
                        "id range is [{}, {}]",
                        db_.get_earliest_block_id().value(),
                        db_.get_latest_block_id().value()));
                }
                return config->start_block_id.value();
            }
            return db_.get_latest_block_id().value_or(0);
        }
        // in memory triedb block id remains 0
        return 0ul;
    }()}
    , mode_{config.has_value() ? Mode::OnDisk : Mode::InMemory}
{
}

TrieDb::TrieDb(
    std::optional<mpt::OnDiskDbConfig> const &config, std::istream &accounts,
    std::istream &code, uint64_t const init_block_number, size_t const buf_size)
    : TrieDb{config}
{
    if (db_.root().is_valid()) {
        throw std::runtime_error(
            "Unable to load snapshot to an existing db, truncate the "
            "existing db to empty and try again");
    }
    if (mode_ == Mode::OnDisk) {
        block_number_ = init_block_number;
    } // was init to 0 and will remain 0 for in memory db
    BinaryDbLoader loader{db_, buf_size, block_number_};
    loader.load(accounts, code);
}

TrieDb::~TrieDb() = default;

std::optional<Account> TrieDb::read_account(Address const &addr)
{
    auto const value =
        db_.get(concat(state_nibble, NibblesView{to_key(addr)}), block_number_);
    if (!value.has_value()) {
        return std::nullopt;
    }

    auto encoded_account = value.value();
    auto acct = decode_account_db(encoded_account);
    MONAD_DEBUG_ASSERT(!acct.has_error());
    MONAD_DEBUG_ASSERT(encoded_account.empty());
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
            state_nibble, NibblesView{to_key(addr)}, NibblesView{to_key(key)}),
        block_number_);
    if (!value.has_value()) {
        STATS_STORAGE_NO_VALUE();
        return {};
    }
    MONAD_ASSERT(value.value().size() <= sizeof(bytes32_t));
    bytes32_t ret;
    std::copy_n(
        value.value().begin(),
        value.value().size(),
        ret.bytes + sizeof(bytes32_t) - value.value().size());
    STATS_STORAGE_VALUE();
    return ret;
};

#ifdef MONAD_TRIEDB_STATS
    #undef STATS_STORAGE_NO_VALUE
    #undef STATS_STORAGE_VALUE
#endif

std::shared_ptr<CodeAnalysis> TrieDb::read_code(bytes32_t const &code_hash)
{
    // TODO read code analysis object
    auto const value = db_.get(
        concat(code_nibble, NibblesView{to_byte_string_view(code_hash.bytes)}),
        block_number_);
    if (!value.has_value()) {
        return std::make_shared<CodeAnalysis>(analyze({}));
    }
    return std::make_shared<CodeAnalysis>(analyze(value.assume_value()));
}

void TrieDb::commit(
    StateDeltas const &state_deltas, Code const &code,
    std::vector<Receipt> const &receipts)
{
    MONAD_ASSERT(mode_ != Mode::OnDiskReadOnly);

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
                            .key = NibblesView{bytes_alloc_.emplace_back(
                                to_key(key))},
                            .value =
                                delta.second == bytes32_t{}
                                    ? std::nullopt
                                    : std::make_optional(rlp::zeroless_view(
                                          to_byte_string_view(
                                              delta.second.bytes))),
                            .incarnation = false,
                            .next = UpdateList{}}));
                }
            }
            value =
                bytes_alloc_.emplace_back(encode_account_db(account.value()));
        }

        if (!storage_updates.empty() || delta.account.first != account) {
            bool const incarnation =
                account.has_value() && delta.account.first.has_value() &&
                delta.account.first->incarnation != account->incarnation;
            account_updates.push_front(update_alloc_.emplace_back(Update{
                .key = NibblesView{bytes_alloc_.emplace_back(to_key(addr))},
                .value = value,
                .incarnation = incarnation,
                .next = std::move(storage_updates)}));
        }
    }

    UpdateList code_updates;
    for (auto const &[hash, code_analysis] : code) {
        // TODO write code analysis object
        MONAD_ASSERT(code_analysis);
        code_updates.push_front(update_alloc_.emplace_back(Update{
            .key = NibblesView{to_byte_string_view(hash.bytes)},
            .value = code_analysis->executable_code,
            .incarnation = false,
            .next = UpdateList{}}));
    }

    UpdateList receipt_updates;
    for (size_t i = 0; i < receipts.size(); ++i) {
        auto const &receipt = receipts[i];
        receipt_updates.push_front(update_alloc_.emplace_back(Update{
            .key =
                NibblesView{bytes_alloc_.emplace_back(rlp::encode_unsigned(i))},
            .value = bytes_alloc_.emplace_back(rlp::encode_receipt(receipt)),
            .incarnation = false,
            .next = UpdateList{}}));
    }
    auto state_update = Update{
        .key = state_nibbles,
        .value = byte_string_view{},
        .incarnation = false,
        .next = std::move(account_updates)};
    auto code_update = Update{
        .key = code_nibbles,
        .value = byte_string_view{},
        .incarnation = false,
        .next = std::move(code_updates)};
    auto receipt_update = Update{
        .key = receipt_nibbles,
        .value = byte_string_view{},
        .incarnation = true,
        .next = std::move(receipt_updates)};
    UpdateList updates;
    updates.push_front(state_update);
    updates.push_front(code_update);
    updates.push_front(receipt_update);
    db_.upsert(std::move(updates), block_number_);
    MONAD_ASSERT(machine_->trie_section == Machine::TrieType::Prefix);

    update_alloc_.clear();
    bytes_alloc_.clear();
}

void TrieDb::increment_block_number()
{
    if (mode_ == Mode::OnDisk) {
        ++block_number_;
    }
}

bytes32_t TrieDb::state_root()
{
    auto const value = db_.get_data(state_nibbles, block_number_);
    if (!value.has_value() || value.value().empty()) {
        return NULL_ROOT;
    }
    bytes32_t root;
    MONAD_ASSERT(value.value().size() == sizeof(bytes32_t));
    std::copy_n(value.value().data(), sizeof(bytes32_t), root.bytes);
    return root;
}

bytes32_t TrieDb::receipts_root()
{
    auto const value = db_.get_data(receipt_nibbles, block_number_);
    if (!value.has_value() || value.value().empty()) {
        return NULL_ROOT;
    }
    bytes32_t root;
    MONAD_ASSERT(value.value().size() == sizeof(bytes32_t));
    std::copy_n(value.value().data(), sizeof(bytes32_t), root.bytes);
    return root;
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

nlohmann::json TrieDb::to_json()
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

        virtual void down(unsigned char const branch, Node const &node) override
        {
            if (branch == INVALID_BRANCH) {
                MONAD_ASSERT(node.path_nibble_view().nibble_size() == 0);
                return;
            }
            path = concat(NibblesView{path}, branch, node.path_nibble_view());

            if (path.nibble_size() == (KECCAK256_SIZE * 2)) {
                handle_account(node);
            }
            else if (
                path.nibble_size() == ((KECCAK256_SIZE + KECCAK256_SIZE) * 2)) {
                handle_storage(node);
            }
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
            MONAD_DEBUG_ASSERT(encoded_account.empty());

            auto const key = fmt::format("{}", NibblesView{path});

            json[key]["balance"] = fmt::format("{}", acct.value().balance);
            json[key]["nonce"] = fmt::format("0x{:x}", acct.value().nonce);

            auto const code_analysis = db.read_code(acct.value().code_hash);
            MONAD_ASSERT(code_analysis);
            json[key]["code"] =
                "0x" + evmc::hex(code_analysis->executable_code);

            if (!json[key].contains("storage")) {
                json[key]["storage"] = nlohmann::json::object();
            }
        }

        void handle_storage(Node const &node)
        {
            MONAD_ASSERT(node.has_value());
            MONAD_ASSERT(node.value().size() <= sizeof(bytes32_t));

            auto const acct_key = fmt::format(
                "{}", NibblesView{path}.substr(0, KECCAK256_SIZE * 2));

            auto const key = fmt::format(
                "{}",
                NibblesView{path}.substr(
                    KECCAK256_SIZE * 2, KECCAK256_SIZE * 2));

            bytes32_t value;
            std::copy_n(
                node.value().begin(),
                node.value().size(),
                value.bytes + sizeof(bytes32_t) - node.value().size());

            json[acct_key]["storage"][key] = fmt::format(
                "0x{:02x}",
                fmt::join(std::as_bytes(std::span(value.bytes)), ""));
        }

        virtual std::unique_ptr<TraverseMachine> clone() const override
        {
            return std::make_unique<Traverse>(*this);
        }
    };

    auto json = nlohmann::json::object();
    Traverse traverse(*this, json);
    // RWOndisk Db prevents any parallel traversal that does blocking i/o
    // from running on the triedb thread, which include to_json. Thus, we can
    // only use blocking traversal for RWOnDisk Db, but can still do parallel
    // traverse in other cases.
    if (mode_ == Mode::OnDisk) {
        MONAD_ASSERT(
            db_.traverse_blocking(state_nibbles, traverse, block_number_));
    }
    else {
        // WARNING: excessive memory usage in parallel traverse
        MONAD_ASSERT(db_.traverse(state_nibbles, traverse, block_number_));
    }

    return json;
}

size_t TrieDb::prefetch_current_root()
{
    size_t const nodes_loaded = db_.prefetch();
    MONAD_ASSERT(machine_->trie_section == Machine::TrieType::Prefix);
    return nodes_loaded;
}

uint64_t TrieDb::get_block_number() const
{
    return block_number_;
}

void TrieDb::set_block_number(uint64_t const n)
{
    MONAD_ASSERT(mode_ == Mode::OnDiskReadOnly);
    block_number_ = n;
}

bool TrieDb::is_latest() const
{
    MONAD_ASSERT(mode_ == Mode::OnDiskReadOnly);
    return db_.is_latest();
}

void TrieDb::load_latest()
{
    MONAD_ASSERT(mode_ == Mode::OnDiskReadOnly);
    db_.load_latest();
}

MONAD_NAMESPACE_END
