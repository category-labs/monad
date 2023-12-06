#include <ethash/keccak.hpp>
#include <monad/core/account_rlp.hpp>
#include <monad/db/config.hpp>
#include <monad/db/in_memory_trie_db.hpp>
#include <monad/rlp/encode2.hpp>

#include <algorithm>

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

MONAD_DB_NAMESPACE_END
