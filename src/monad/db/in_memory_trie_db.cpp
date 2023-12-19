#include <monad/core/account_rlp.hpp>
#include <monad/core/bytes_fmt.hpp>
#include <monad/core/int.hpp>
#include <monad/core/int_fmt.hpp>
#include <monad/db/config.hpp>
#include <monad/db/in_memory_trie_db.hpp>
#include <monad/mpt/nibbles_view_fmt.hpp>
#include <monad/mpt/traverse.hpp>
#include <monad/rlp/encode2.hpp>

#include <ethash/keccak.hpp>
#include <evmc/evmc.hpp>

#include <algorithm>
#include <cstdlib>

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

    class TrieStateMachine final : public StateMachine
    {
    private:
        uint8_t depth = 0;
        bool is_merkle = false;

    public:
        virtual std::unique_ptr<StateMachine> clone() const override
        {
            return std::make_unique<TrieStateMachine>();
        }

        virtual void down(unsigned char const nibble) override
        {
            ++depth;
            MONAD_DEBUG_ASSERT(
                (nibble == state_nibble || nibble == code_nibble) ||
                depth != 1);
            if (MONAD_UNLIKELY(depth == 1 && nibble == state_nibble)) {
                is_merkle = true;
            }
        }

        virtual void up(size_t const n) override
        {
            MONAD_DEBUG_ASSERT(n <= depth);
            depth -= static_cast<uint8_t>(n);
            if (MONAD_UNLIKELY(is_merkle && depth < 1)) {
                is_merkle = false;
            }
        }

        virtual Compute &get_compute() override
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

        virtual CacheOption get_cache_option() const override
        {
            return CacheOption::CacheAll;
        }
    };

    static_assert(sizeof(TrieStateMachine) == 16);
}

InMemoryTrieDB::InMemoryTrieDB(nlohmann::json const &json)
{
    UpdateList account_updates;
    UpdateList code_updates;
    for (auto const &[key, value] : json.items()) {
        UpdateList storage_updates;
        for (auto const &[storage_key, storage_value] :
             value.at("storage").items()) {
            storage_updates.push_front(update_alloc_.emplace_back(Update{
                .key = bytes_alloc_.emplace_back(
                    evmc::from_hex(storage_key).value()),
                .value = bytes_alloc_.emplace_back(
                    evmc::from_hex(storage_value.get<std::string>()).value()),
                .incarnation = false,
                .next = UpdateList{}}));
        }
        auto const &code = bytes_alloc_.emplace_back(
            evmc::from_hex(value.at("code").get<std::string>()).value());
        auto const acct = Account{
            .balance = intx::from_string<uint256_t>(value.at("balance")),
            .code_hash = std::bit_cast<bytes32_t>(
                ethash::keccak256(code.data(), code.size())),
            .nonce =
                std::stoull(value.at("nonce").get<std::string>(), nullptr, 16)};
        account_updates.push_front(update_alloc_.emplace_back(Update{
            .key = bytes_alloc_.emplace_back(evmc::from_hex(key).value()),
            .value = bytes_alloc_.emplace_back(rlp::encode_account(acct)),
            .incarnation = false,
            .next = std::move(storage_updates)}));

        code_updates.push_front(update_alloc_.emplace_back(Update{
            .key = bytes_alloc_.emplace_back(
                to_byte_string_view(acct.code_hash.bytes)),
            .value = code,
            .incarnation = false,
            .next = UpdateList{}}));
    }
    UpdateList updates;
    Update state_update{
        .key = state_nibbles,
        .value = byte_string_view{},
        .incarnation = false,
        .next = std::move(account_updates)};
    Update code_update{
        .key = code_nibbles,
        .value = byte_string_view{},
        .incarnation = false,
        .next = std::move(code_updates)};
    updates.push_front(state_update);
    updates.push_front(code_update);

    UpdateAux aux;
    TrieStateMachine state_machine;
    root_ = upsert(aux, state_machine, std::move(root_), std::move(updates));
    MONAD_DEBUG_ASSERT(root_);

    update_alloc_.clear();
    bytes_alloc_.clear();
}

std::optional<Account> InMemoryTrieDB::read_account(Address const &addr) const
{
    UpdateAux aux;
    auto const [node, result] = find_blocking(
        aux, root_.get(), concat(state_nibble, NibblesView{to_key(addr)}));
    if (result != find_result::success) {
        return std::nullopt;
    }
    MONAD_DEBUG_ASSERT(node != nullptr);
    Account acct;
    auto const decode_result = rlp::decode_account(acct, node->value());
    MONAD_DEBUG_ASSERT(decode_result.has_value());
    MONAD_DEBUG_ASSERT(decode_result.assume_value().empty());
    return acct;
}

bytes32_t
InMemoryTrieDB::read_storage(Address const &addr, bytes32_t const &key) const
{
    UpdateAux aux;
    auto const [node, result] = find_blocking(
        aux,
        root_.get(),
        concat(
            state_nibble, NibblesView{to_key(addr)}, NibblesView{to_key(key)}));
    if (result != find_result::success) {
        return {};
    }
    MONAD_DEBUG_ASSERT(node != nullptr);
    MONAD_DEBUG_ASSERT(node->value().size() == sizeof(bytes32_t));
    bytes32_t value;
    std::copy_n(node->value().begin(), sizeof(bytes32_t), value.bytes);
    return value;
};

byte_string InMemoryTrieDB::read_code(bytes32_t const &hash) const
{
    UpdateAux aux;
    auto const [node, result] = find_blocking(
        aux,
        root_.get(),
        concat(code_nibble, NibblesView{to_byte_string_view(hash.bytes)}));
    if (result != find_result::success) {
        return byte_string{};
    }
    return byte_string{node->value()};
}

void InMemoryTrieDB::commit(StateDeltas const &state_deltas, Code const &code)
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
    UpdateAux aux;
    TrieStateMachine state_machine;
    root_ = upsert(aux, state_machine, std::move(root_), std::move(updates));

    update_alloc_.clear();
    bytes_alloc_.clear();
}

void InMemoryTrieDB::create_and_prune_block_history(uint64_t) const {

};

bytes32_t InMemoryTrieDB::state_root() const
{
    bytes32_t root = NULL_ROOT;
    UpdateAux aux;
    auto const [node, result] = find_blocking(aux, root_.get(), state_nibbles);
    if (result != find_result::success || node->number_of_children() == 0) {
        return root;
    }
    MONAD_DEBUG_ASSERT(node->data().size() == sizeof(bytes32_t));
    std::copy_n(node->data().data(), sizeof(bytes32_t), root.bytes);
    return root;
}

nlohmann::json InMemoryTrieDB::to_json() const
{
    struct Traverse : public TraverseMachine
    {
        InMemoryTrieDB const &db;
        nlohmann::json json;
        Nibbles path;

        Traverse(InMemoryTrieDB const &db)
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

            json[acct_key]["storage"][key] = fmt::format("{}", value);
        }
    } traverse(*this);

    UpdateAux aux;
    auto const [node, result] = find_blocking(aux, root_.get(), state_nibbles);
    if (result == find_result::success) {
        MONAD_DEBUG_ASSERT(node);
        preorder_traverse(*node, traverse);
    }
    return traverse.json;
}

MONAD_DB_NAMESPACE_END
