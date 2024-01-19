#include <monad/core/account_rlp.hpp>
#include <monad/core/bytes_fmt.hpp>
#include <monad/core/int.hpp>
#include <monad/core/int_fmt.hpp>
#include <monad/db/config.hpp>
#include <monad/db/trie_db.hpp>
#include <monad/mpt/nibbles_view_fmt.hpp>
#include <monad/mpt/traverse.hpp>
#include <monad/rlp/encode2.hpp>

#include <boost/json.hpp>
#include <boost/json/basic_parser_impl.hpp>
#include <ethash/keccak.hpp>
#include <evmc/evmc.hpp>

#include <nlohmann/json.hpp>

#include <algorithm>
#include <chrono>
#include <cstdlib>
#include <set>

MONAD_DB_NAMESPACE_BEGIN

using namespace monad::mpt;

namespace
{
    constexpr unsigned char state_nibble = 0;
    constexpr unsigned char code_nibble = 1;
    auto const state_nibbles = concat(state_nibble);
    auto const code_nibbles = concat(code_nibble);

    template <class T>
        requires std::same_as<T, bytes32_t> || std::same_as<T, Address>
    constexpr byte_string to_key(T const &arg)
    {
        return byte_string{
            std::bit_cast<bytes32_t>(
                ethash::keccak256(arg.bytes, sizeof(arg.bytes)))
                .bytes,
            sizeof(bytes32_t)};
    }

    struct LeafCompute
    {
        static byte_string compute(Node const &node)
        {
            MONAD_DEBUG_ASSERT(node.has_value());

            // this is the block number leaf
            if (MONAD_UNLIKELY(node.value().empty())) {
                return {};
            }
            // this is a storage leaf
            else if (node.value().size() == sizeof(bytes32_t)) {
                return rlp::encode_string2(rlp::zeroless_view(node.value()));
            }

            MONAD_DEBUG_ASSERT(node.value().size() > sizeof(bytes32_t));

            Account acc;
            auto const result = rlp::decode_account(acc, node.value());
            MONAD_DEBUG_ASSERT(result.has_value());
            MONAD_DEBUG_ASSERT(result.assume_value().empty());
            bytes32_t storage_root = NULL_ROOT;
            if (node.number_of_children()) {
                MONAD_DEBUG_ASSERT(node.data().size() == sizeof(bytes32_t));
                std::copy_n(
                    node.data().data(), sizeof(bytes32_t), storage_root.bytes);
            }
            return rlp::encode_account(acc, storage_root);
        }
    };

    using MerkleCompute = MerkleComputeBase<LeafCompute>;

    struct EmptyCompute : public Compute
    {
        virtual unsigned compute_len(std::span<ChildData>, uint16_t) override
        {
            return 0;
        };

        virtual unsigned compute_branch(unsigned char *, Node *) override
        {
            return 0;
        };

        virtual unsigned compute(unsigned char *, Node *) override
        {
            return 0;
        };
    };

    struct JsonDbLoader
    {
        static constexpr size_t max_object_size = std::size_t(-1);
        static constexpr size_t max_array_size = std::size_t(-1);
        static constexpr size_t max_key_size = std::size_t(-1);
        static constexpr size_t max_string_size = std::size_t(-1);
        static constexpr size_t bytes32_size = sizeof(bytes32_t) * 2 + 2;

        enum class State
        {
            Root = 0,
            Accounts,
            Account,
            Balance,
            Code,
            Nonce,
            Storage
        } state_;

        std::string key_;
        std::string value_;
        byte_string acct_key_;
        Account acct_;
        std::list<mpt::Update> update_alloc_;
        std::list<byte_string> bytes_alloc_;
        UpdateList account_updates_;
        UpdateList code_updates_;
        ::monad::mpt::Db &db_;
        size_t batch_size_;
        UpdateList storage_updates_;
        std::set<bytes32_t> inserted_code_;

        JsonDbLoader(::monad::mpt::Db &db, size_t batch_size)
            : state_{State::Root}
            , db_{db}
            , batch_size_{batch_size}
        {
        }

        bool on_document_begin(std::error_code &)
        {
            MONAD_ASSERT(state_ == State::Root);
            return true;
        }

        bool on_document_end(std::error_code &)
        {
            MONAD_ASSERT(state_ == State::Root);
            return true;
        }

        bool on_object_begin(std::error_code &)
        {
            if (state_ == State::Root) {
                state_ = State::Accounts;
            }
            else if (state_ == State::Accounts) {
                state_ = State::Account;
            }
            else if (state_ == State::Account) {
                state_ = State::Storage;
            }
            else {
                MONAD_ASSERT(false);
            }
            return true;
        }

        bool on_object_end(size_t, std::error_code &)
        {
            if (state_ == State::Accounts) {
                state_ = State::Root;
            }
            else if (state_ == State::Account) {
                account_updates_.push_front(update_alloc_.emplace_back(Update{
                    .key = bytes_alloc_.emplace_back(acct_key_),
                    .value =
                        bytes_alloc_.emplace_back(rlp::encode_account(acct_)),
                    .incarnation = false,
                    .next = std::move(storage_updates_)}));
                storage_updates_.clear();

                if (account_updates_.size() >= batch_size_) {
                    static_assert(UpdateList::constant_time_size);
                    write();
                }
                state_ = State::Accounts;
            }
            else if (state_ == State::Storage) {
                state_ = State::Account;
            }
            else {
                MONAD_ASSERT(false);
            }
            return true;
        }

        bool on_array_begin(std::error_code &)
        {
            return false;
        }

        bool on_array_end(size_t, std::error_code &)
        {
            return false;
        }

        bool on_key_part(std::string_view in, size_t n, std::error_code &)
        {
            append_to(key_, in, n);
            return true;
        }

        bool on_key(std::string_view in, size_t n, std::error_code &)
        {
            append_to(key_, in, n);

            if (state_ == State::Accounts) {
                MONAD_ASSERT(n == bytes32_size);
                acct_key_ = evmc::from_hex(key_).value();
                key_.clear();
            }
            else if (state_ == State::Account) {
                if (key_ == "balance") {
                    state_ = State::Balance;
                }
                else if (key_ == "nonce") {
                    state_ = State::Nonce;
                }
                else if (key_ == "code") {
                    state_ = State::Code;
                }
                else if (key_ != "storage") {
                    MONAD_ASSERT(false);
                }
                key_.clear();
            }
            else if (state_ == State::Storage) {
                MONAD_ASSERT(n == bytes32_size);
            }
            else {
                MONAD_ASSERT(false);
            }

            return true;
        }

        bool on_string_part(std::string_view in, size_t n, std::error_code &)
        {
            append_to(value_, in, n);
            return true;
        }

        bool on_string(std::string_view in, size_t n, std::error_code &)
        {
            append_to(value_, in, n);
            if (state_ == State::Balance) {
                state_ = State::Account;
                acct_.balance = intx::from_string<uint256_t>(value_);
            }
            else if (state_ == State::Code) {
                state_ = State::Account;
                auto const &code =
                    bytes_alloc_.emplace_back(evmc::from_hex(value_).value());
                acct_.code_hash = std::bit_cast<bytes32_t>(
                    ethash::keccak256(code.data(), code.size()));
                if (!inserted_code_.contains(acct_.code_hash)) {
                    if (acct_.code_hash != NULL_HASH) {
                        code_updates_.push_front(
                            update_alloc_.emplace_back(Update{
                                .key = bytes_alloc_.emplace_back(
                                    to_byte_string_view(acct_.code_hash.bytes)),
                                .value = code,
                                .incarnation = false,
                                .next = UpdateList{}}));
                    }
                    inserted_code_.insert(acct_.code_hash);
                }
            }
            else if (state_ == State::Nonce) {
                state_ = State::Account;
                acct_.nonce = std::stoull(value_, nullptr, 16);
            }
            else if (state_ == State::Storage) {
                MONAD_ASSERT(value_.size() == bytes32_size);
                storage_updates_.push_front(update_alloc_.emplace_back(Update{
                    .key =
                        bytes_alloc_.emplace_back(evmc::from_hex(key_).value()),
                    .value = bytes_alloc_.emplace_back(
                        evmc::from_hex(value_).value()),
                    .incarnation = false,
                    .next = UpdateList{}}));
                key_.clear();
            }
            else {
                MONAD_ASSERT(false);
            }

            value_.clear();
            return true;
        }

        bool on_number_part(std::string_view, std::error_code &)
        {
            return false;
        }

        bool on_int64(std::int64_t, std::string_view, std::error_code &)
        {
            return false;
        }

        bool on_uint64(std::uint64_t, std::string_view, std::error_code &)
        {
            return false;
        }

        bool on_double(double, std::string_view, std::error_code &)
        {
            return false;
        }

        bool on_bool(bool, std::error_code &)
        {
            return false;
        }

        bool on_null(std::error_code &)
        {
            return false;
        }

        bool on_comment_part(std::string_view, std::error_code &)
        {
            return false;
        }

        bool on_comment(std::string_view, std::error_code &)
        {
            return false;
        }

        void append_to(std::string &to, std::string_view in, size_t n)
        {
            to.append(in);
            MONAD_ASSERT(to.size() == n);
        }

        void write()
        {
            UpdateList updates;
            updates.push_front(update_alloc_.emplace_back(Update{
                .key = state_nibbles,
                .value = byte_string_view{},
                .incarnation = false,
                .next = std::move(account_updates_)}));
            updates.push_front(update_alloc_.emplace_back(Update{
                .key = code_nibbles,
                .value = byte_string_view{},
                .incarnation = false,
                .next = std::move(code_updates_)}));

            db_.upsert(std::move(updates));

            inserted_code_.clear();
            account_updates_.clear();
            code_updates_.clear();
            update_alloc_.clear();
            bytes_alloc_.clear();
        }
    };
}

std::unique_ptr<StateMachine> TrieDb::Machine::clone() const
{
    return std::make_unique<Machine>();
}

void TrieDb::Machine::down(unsigned char const nibble)
{
    ++depth;
    MONAD_DEBUG_ASSERT(
        (nibble == state_nibble || nibble == code_nibble) || depth != 1);
    if (MONAD_UNLIKELY(depth == 1 && nibble == state_nibble)) {
        is_merkle = true;
    }
}

void TrieDb::Machine::up(size_t const n)
{
    MONAD_DEBUG_ASSERT(n <= depth);
    depth -= static_cast<uint8_t>(n);
    if (MONAD_UNLIKELY(is_merkle && depth < 1)) {
        is_merkle = false;
    }
}

Compute &TrieDb::Machine::get_compute()
{
    static EmptyCompute empty;
    static MerkleCompute merkle;
    if (MONAD_LIKELY(is_merkle)) {
        return merkle;
    }
    else {
        return empty;
    }
}

bool TrieDb::Machine::cache() const
{
    return true;
}

TrieDb::TrieDb(mpt::DbOptions const &options)
    : db_{machine_, options}
{
}

TrieDb::TrieDb(DbOptions const &options, std::istream &input, size_t batch_size)
    : TrieDb{options}
{
    boost::json::basic_parser<JsonDbLoader> parser{
        boost::json::parse_options{}, db_, batch_size};

    char buf[4096];
    std::error_code ec;
    while (input.read(buf, sizeof(buf))) {
        auto const count = static_cast<size_t>(input.gcount());
        MONAD_ASSERT(count <= sizeof(buf));
        parser.write_some(true, buf, count, ec);
        MONAD_ASSERT(!ec);
    }
    auto const count = static_cast<size_t>(input.gcount());
    MONAD_ASSERT(count <= sizeof(buf));
    parser.write_some(false, buf, count, ec);
    MONAD_ASSERT(!ec);
    MONAD_ASSERT(input.eof());
    MONAD_ASSERT(parser.done());

    parser.handler().write();
    MONAD_DEBUG_ASSERT(machine_.depth == 0 && machine_.is_merkle == false);
}

std::optional<Account> TrieDb::read_account(Address const &addr)
{
    auto const value = db_.get(concat(state_nibble, NibblesView{to_key(addr)}));
    if (!value.has_value()) {
        return std::nullopt;
    }
    Account acct{.incarnation = 0};
    auto const decode_result = rlp::decode_account(acct, value.value());
    MONAD_DEBUG_ASSERT(decode_result.has_value());
    MONAD_DEBUG_ASSERT(decode_result.assume_value().empty());
    return acct;
}

bytes32_t TrieDb::read_storage(Address const &addr, bytes32_t const &key)
{
    auto const value = db_.get(concat(
        state_nibble, NibblesView{to_key(addr)}, NibblesView{to_key(key)}));
    if (!value.has_value()) {
        return {};
    }
    MONAD_DEBUG_ASSERT(value.value().size() == sizeof(bytes32_t));
    bytes32_t ret;
    std::copy_n(value.value().begin(), sizeof(bytes32_t), ret.bytes);
    return ret;
};

byte_string TrieDb::read_code(bytes32_t const &hash)
{
    auto const value = db_.get(
        concat(code_nibble, NibblesView{to_byte_string_view(hash.bytes)}));
    if (!value.has_value()) {
        return byte_string{};
    }
    return byte_string{value.value()};
}

void TrieDb::commit(StateDeltas const &state_deltas, Code const &code)
{
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
                                    : std::make_optional(to_byte_string_view(
                                          delta.second.bytes)),
                            .incarnation = false,
                            .next = UpdateList{}}));
                }
            }
            value =
                bytes_alloc_.emplace_back(rlp::encode_account(account.value()));
        }

        if (!storage_updates.empty() || delta.account.first != account) {
            account_updates.push_front(update_alloc_.emplace_back(Update{
                .key = NibblesView{bytes_alloc_.emplace_back(to_key(addr))},
                .value = value,
                .incarnation = account.has_value()
                                   ? account.value().incarnation != 0
                                   : false,
                .next = std::move(storage_updates)}));
        }
    }

    UpdateList code_updates;
    for (auto const &[hash, bytes] : code) {
        code_updates.push_front(update_alloc_.emplace_back(Update{
            .key = NibblesView{to_byte_string_view(hash.bytes)},
            .value = bytes,
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
    UpdateList updates;
    updates.push_front(state_update);
    updates.push_front(code_update);
    db_.upsert(std::move(updates));
    MONAD_DEBUG_ASSERT(machine_.depth == 0 && machine_.is_merkle == false);

    update_alloc_.clear();
    bytes_alloc_.clear();
}

void TrieDb::create_and_prune_block_history(uint64_t) const {

};

bytes32_t TrieDb::state_root()
{
    auto const value = db_.get_data(state_nibbles);
    if (!value.has_value() || value.value().empty()) {
        return NULL_ROOT;
    }
    bytes32_t root;
    MONAD_DEBUG_ASSERT(value.value().size() == sizeof(bytes32_t));
    std::copy_n(value.value().data(), sizeof(bytes32_t), root.bytes);
    return root;
}

nlohmann::json TrieDb::to_json()
{
    struct Traverse : public TraverseMachine
    {
        TrieDb &db;
        nlohmann::json json;
        Nibbles path;

        Traverse(TrieDb &db)
            : db(db)
            , json(nlohmann::json::object())
            , path()
        {
        }

        virtual void down(unsigned char const branch, Node const &node) override
        {
            if (branch == INVALID_BRANCH) {
                MONAD_DEBUG_ASSERT(node.path_nibble_view().nibble_size() == 0);
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
                    MONAD_DEBUG_ASSERT(path_view.nibble_size() == 0);
                    return 0;
                }
                int const rem_size = path_view.nibble_size() - 1 -
                                     node.path_nibble_view().nibble_size();
                MONAD_DEBUG_ASSERT(rem_size >= 0);
                MONAD_DEBUG_ASSERT(
                    path_view.substr(static_cast<unsigned>(rem_size)) ==
                    concat(branch, node.path_nibble_view()));
                return rem_size;
            }();
            path = path_view.substr(0, static_cast<unsigned>(rem_size));
        }

        void handle_account(Node const &node)
        {
            MONAD_DEBUG_ASSERT(node.has_value());

            Account acct;
            auto const result = rlp::decode_account(acct, node.value());
            MONAD_DEBUG_ASSERT(result.has_value());
            MONAD_DEBUG_ASSERT(result.assume_value().empty());

            auto const key = fmt::format("{}", NibblesView{path});

            json[key]["balance"] = fmt::format("{}", acct.balance);
            json[key]["nonce"] = fmt::format("0x{:x}", acct.nonce);

            auto const code = db.read_code(acct.code_hash);
            json[key]["code"] = fmt::format(
                "0x{:02x}", fmt::join(std::as_bytes(std::span(code)), ""));

            if (!json[key].contains("storage")) {
                json[key]["storage"] = nlohmann::json::object();
            }
        }

        void handle_storage(Node const &node)
        {
            MONAD_DEBUG_ASSERT(node.has_value());
            MONAD_DEBUG_ASSERT(node.value().size() == sizeof(bytes32_t));

            auto const acct_key = fmt::format(
                "{}", NibblesView{path}.substr(0, KECCAK256_SIZE * 2));

            auto const key = fmt::format(
                "{}",
                NibblesView{path}.substr(
                    KECCAK256_SIZE * 2, KECCAK256_SIZE * 2));

            bytes32_t value;
            std::copy_n(node.value().begin(), sizeof(bytes32_t), value.bytes);

            json[acct_key]["storage"][key] = fmt::format(
                "0x{:02x}",
                fmt::join(std::as_bytes(std::span(value.bytes)), ""));
        }
    } traverse(*this);

    db_.traverse(state_nibbles, traverse);

    return traverse.json;
}

MONAD_DB_NAMESPACE_END
