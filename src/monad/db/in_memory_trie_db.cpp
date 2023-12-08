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

namespace
{
    constexpr auto state_prefix = byte_string{0x00};

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
}

byte_string Compute::compute(mpt::Node const &node)
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
        std::copy_n(node.data().data(), sizeof(bytes32_t), storage_root.bytes);
    }
    return rlp::encode_account(acc, storage_root);
}

std::unique_ptr<mpt::TrieStateMachine> EmptyStateMachine::clone() const
{
    return std::make_unique<EmptyStateMachine>();
}

void EmptyStateMachine::reset(std::optional<uint8_t>) {}

void EmptyStateMachine::forward(byte_string_view) {}

void EmptyStateMachine::backward() {}

mpt::Compute &EmptyStateMachine::get_compute()
{
    return compute_;
}

mpt::Compute &EmptyStateMachine::get_compute(uint8_t)
{
    return compute_;
}

uint8_t EmptyStateMachine::get_state() const
{
    return 0;
}

mpt::CacheOption EmptyStateMachine::cache_option() const
{
    return mpt::CacheOption::CacheAll;
}

InMemoryTrieDB::InMemoryTrieDB(nlohmann::json const &json)
{
    mpt::UpdateList account_updates;
    for (auto const &[key, value] : json.items()) {
        mpt::UpdateList storage_updates;
        for (auto const &[storage_key, storage_value] :
             value.at("storage").items()) {
            storage_updates.push_front(
                update_allocator_.emplace_back(mpt::Update{
                    .key = byte_string_allocator_.emplace_back(
                        evmc::from_hex(storage_key).value()),
                    .value = byte_string_allocator_.emplace_back(
                        evmc::from_hex(storage_value.get<std::string>())
                            .value()),
                    .incarnation = false,
                    .next = mpt::UpdateList{}}));
        }
        auto const code =
            evmc::from_hex(value.at("code").get<std::string>()).value();
        auto const acct = Account{
            .balance = intx::from_string<uint256_t>(value.at("balance")),
            .code_hash = std::bit_cast<bytes32_t>(
                ethash::keccak256(code.data(), code.size())),
            .nonce = std::stoull(value.at("nonce").get<std::string>())};
        account_updates.push_front(update_allocator_.emplace_back(mpt::Update{
            .key = byte_string_allocator_.emplace_back(
                evmc::from_hex(key).value()),
            .value =
                byte_string_allocator_.emplace_back(rlp::encode_account(acct)),
            .incarnation = false,
            .next = std::move(storage_updates)}));
        code_.try_emplace(acct.code_hash, code);
    }
    mpt::UpdateList updates;
    mpt::Update update{
        .key = mpt::NibblesView{state_prefix},
        .value = byte_string_view{},
        .incarnation = false,
        .next = std::move(account_updates)};
    updates.push_front(update);

    mpt::UpdateAux aux;
    EmptyStateMachine state_machine;
    root_ = upsert(aux, state_machine, std::move(root_), std::move(updates));
    MONAD_DEBUG_ASSERT(root_);

    update_allocator_.clear();
    byte_string_allocator_.clear();
}

std::optional<Account> InMemoryTrieDB::read_account(Address const &addr) const
{
    auto const [node, result] =
        mpt::find_blocking(nullptr, root_.get(), state_prefix + to_key(addr));
    if (result != mpt::find_result::success) {
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
    auto const [node, result] = mpt::find_blocking(
        nullptr, root_.get(), state_prefix + to_key(addr) + to_key(key));
    if (result != mpt::find_result::success) {
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
    if (code_.contains(hash)) {
        return code_.at(hash);
    }
    return byte_string{};
}

void InMemoryTrieDB::commit(StateDeltas const &state_deltas, Code const &code)
{
    mpt::UpdateList account_updates;
    for (auto const &[addr, delta] : state_deltas) {
        mpt::UpdateList storage_updates;
        std::optional<byte_string_view> value;
        auto const &account = delta.account.second;
        if (account.has_value()) {
            for (auto const &[key, delta] : delta.storage) {
                if (delta.first != delta.second) {
                    storage_updates.push_front(
                        update_allocator_.emplace_back(mpt::Update{
                            .key =
                                mpt::NibblesView{
                                    byte_string_allocator_.emplace_back(
                                        to_key(key))},
                            .value =
                                delta.second == bytes32_t{}
                                    ? std::nullopt
                                    : std::make_optional(to_byte_string_view(
                                          delta.second.bytes)),
                            .incarnation = false,
                            .next = mpt::UpdateList{}}));
                }
            }
            value = byte_string_allocator_.emplace_back(
                rlp::encode_account(account.value()));
        }

        if (!storage_updates.empty() || delta.account.first != account) {
            account_updates.push_front(
                update_allocator_.emplace_back(mpt::Update{
                    .key = mpt::NibblesView{byte_string_allocator_.emplace_back(
                        to_key(addr))},
                    .value = value,
                    .incarnation = account.has_value()
                                       ? account.value().incarnation != 0
                                       : false,
                    .next = std::move(storage_updates)}));
        }
    }

    for (auto const &[hash, bytes] : code) {
        code_[hash] = bytes;
    }

    auto state_update = mpt::Update{
        .key = mpt::NibblesView{state_prefix},
        .value = byte_string_view{},
        .incarnation = false,
        .next = std::move(account_updates)};
    mpt::UpdateList updates;
    updates.push_front(state_update);
    mpt::UpdateAux aux;
    EmptyStateMachine state_machine;
    root_ = upsert(aux, state_machine, std::move(root_), std::move(updates));

    update_allocator_.clear();
    byte_string_allocator_.clear();
}

void InMemoryTrieDB::create_and_prune_block_history(uint64_t) const {

};

bytes32_t InMemoryTrieDB::state_root() const
{
    bytes32_t root = NULL_ROOT;
    if (root_ && root_->number_of_children()) {
        MONAD_DEBUG_ASSERT(root_->data().size() == sizeof(bytes32_t));
        std::copy_n(root_->data().data(), sizeof(bytes32_t), root.bytes);
    }
    return root;
}

nlohmann::json InMemoryTrieDB::to_json() const
{
    struct Traverse : public mpt::TraverseMachine
    {
        InMemoryTrieDB const &db;
        nlohmann::json json;
        mpt::Nibbles path;

        Traverse(InMemoryTrieDB const &db)
            : db(db)
            , json(nlohmann::json::object())
            , path()
        {
        }

        virtual void
        down(unsigned char const branch, mpt::Node const &node) override
        {
            path = branch == mpt::INVALID_BRANCH
                       ? concat(mpt::NibblesView{path}, node.path_nibble_view())
                       : concat(
                             mpt::NibblesView{path},
                             branch,
                             node.path_nibble_view());
            auto const view = mpt::NibblesView{path};

            if (view.nibble_size() <= (state_prefix.size() * 2)) {
                return;
            }

            MONAD_DEBUG_ASSERT(
                view.substr(0, state_prefix.size() * 2) ==
                mpt::NibblesView{state_prefix});

            if (view.nibble_size() ==
                ((state_prefix.size() + KECCAK256_SIZE) * 2)) {
                handle_account(node);
            }
            else if (
                view.nibble_size() ==
                ((state_prefix.size() + KECCAK256_SIZE + KECCAK256_SIZE) * 2)) {
                handle_storage(node);
            }
        }

        virtual void
        up(unsigned char const branch, mpt::Node const &node) override
        {
            auto const path_view = mpt::NibblesView{path};
            auto const rem_size = [&] {
                if (branch == mpt::INVALID_BRANCH) {
                    int const rem_size = path_view.nibble_size() -
                                         node.path_nibble_view().nibble_size();
                    MONAD_DEBUG_ASSERT(rem_size >= 0);
                    MONAD_DEBUG_ASSERT(
                        path_view.substr(static_cast<unsigned>(rem_size)) ==
                        node.path_nibble_view());
                    return rem_size;
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

        void handle_account(mpt::Node const &node)
        {
            MONAD_DEBUG_ASSERT(node.has_value());

            Account acct;
            auto const result = rlp::decode_account(acct, node.value());
            MONAD_DEBUG_ASSERT(result.has_value());
            MONAD_DEBUG_ASSERT(result.assume_value().empty());

            auto const key = fmt::format(
                "{}",
                mpt::NibblesView{path}.substr(
                    state_prefix.size() * 2, KECCAK256_SIZE * 2));

            json[key]["balance"] = fmt::format("{}", acct.balance);
            json[key]["nonce"] = fmt::format("0x{:x}", acct.nonce);

            auto const code = db.read_code(acct.code_hash);
            json[key]["code"] = fmt::format(
                "0x{:02x}", fmt::join(std::as_bytes(std::span(code)), ""));

            if (!json[key].contains("storage")) {
                json[key]["storage"] = nlohmann::json::object();
            }
        }

        void handle_storage(mpt::Node const &node)
        {
            MONAD_DEBUG_ASSERT(node.has_value());
            MONAD_DEBUG_ASSERT(node.value().size() == sizeof(bytes32_t));

            auto const acct_key = fmt::format(
                "{}",
                mpt::NibblesView{path}.substr(
                    state_prefix.size() * 2, KECCAK256_SIZE * 2));

            auto const key = fmt::format(
                "{}",
                mpt::NibblesView{path}.substr(
                    (state_prefix.size() + KECCAK256_SIZE) * 2,
                    KECCAK256_SIZE * 2));

            bytes32_t value;
            std::copy_n(node.value().begin(), sizeof(bytes32_t), value.bytes);

            json[acct_key]["storage"][key] = fmt::format("{}", value);
        }
    } traverse(*this);

    mpt::preorder_traverse(*root_, traverse);
    return traverse.json;
}

MONAD_DB_NAMESPACE_END
