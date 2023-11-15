#pragma once

#include <monad/core/account_rlp.hpp>
#include <monad/db/config.hpp>
#include <monad/db/db.hpp>
#include <monad/mpt/compute.hpp>
#include <monad/mpt/trie.hpp>

#include <ankerl/unordered_dense.h>

#include <list>

MONAD_DB_NAMESPACE_BEGIN

class EmptyStateMachine final : public mpt::TrieStateMachine
{
public:
    virtual std::unique_ptr<TrieStateMachine> clone() const override
    {
        return std::make_unique<EmptyStateMachine>();
    }

    virtual void reset(std::optional<uint8_t>) override {}

    virtual void forward(byte_string_view) override {}

    virtual void backward() override {}

    virtual mpt::Compute &get_compute() const override
    {
        // TODO: refactor this API so that compute_ is a member func
        static mpt::EmptyCompute compute_;
        return compute_;
    }

    virtual uint8_t get_state() const override
    {
        return 0;
    }

    virtual mpt::CacheOption cache_option() const override
    {
        return mpt::CacheOption::CacheAll;
    }
};

class InMemoryTrieDB final : public Db
{
private:
    static constexpr auto state_prefix = byte_string{0x00};
    mpt::node_ptr root_;
    std::list<mpt::Update> update_allocator_;
    std::list<byte_string> byte_string_allocator_;
    ankerl::unordered_dense::segmented_map<bytes32_t, byte_string> code_;

public:
    InMemoryTrieDB()
        : root_(nullptr)
    {
    }

    [[nodiscard]] virtual std::optional<Account>
    read_account(address_t const &addr) const override
    {
        auto const [node, result] = mpt::find_blocking(
            nullptr,
            root_.get(),
            state_prefix + byte_string{to_byte_string_view(addr.bytes)});
        if (result != mpt::find_result::success) {
            return std::nullopt;
        }
        MONAD_DEBUG_ASSERT(node != nullptr);
        Account acct;
        rlp::decode_account(acct, node->leaf_view());
        return acct;
    }

    [[nodiscard]] virtual bytes32_t
    read_storage(address_t const &addr, bytes32_t const &key) const override
    {
        auto const [node, result] = mpt::find_blocking(
            nullptr,
            root_.get(),
            state_prefix + byte_string{to_byte_string_view(addr.bytes)} +
                byte_string{to_byte_string_view(key.bytes)});
        if (result != mpt::find_result::success) {
            return {};
        }
        MONAD_DEBUG_ASSERT(node != nullptr);
        MONAD_DEBUG_ASSERT(node->leaf_view().size() == sizeof(bytes32_t));
        bytes32_t value;
        std::copy_n(node->leaf_view().begin(), sizeof(bytes32_t), value.bytes);
        return value;
    };

    [[nodiscard]] virtual byte_string
    read_code(bytes32_t const &hash) const override
    {
        if (code_.contains(hash)) {
            return code_.at(hash);
        }
        return byte_string{};
    }

    virtual void
    commit(StateDeltas const &state_deltas, Code const &code) override
    {
        mpt::UpdateList account_updates;
        for (auto const &[addr, delta] : state_deltas) {
            mpt::UpdateList storage_updates;
            std::optional<byte_string_view> value;
            auto const &account = delta.account.second;
            if (account.has_value()) {
                for (auto const &[key, delta] : delta.storage) {
                    storage_updates.push_front(
                        update_allocator_.emplace_back(mpt::Update{
                            .key = mpt::NibblesView{to_byte_string_view(
                                key.bytes)},
                            .value = to_byte_string_view(delta.second.bytes),
                            .incarnation = false,
                            .next = mpt::UpdateList{}}));
                }
                value = byte_string_allocator_.emplace_back(
                    rlp::encode_account(account.value()));
            }

            if (!storage_updates.empty() || delta.account.first != account) {
                account_updates.push_front(
                    update_allocator_.emplace_back(mpt::Update{
                        .key =
                            mpt::NibblesView{to_byte_string_view(addr.bytes)},
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
        root_ = upsert(aux, state_machine, root_.get(), std::move(updates));

        update_allocator_.clear();
        byte_string_allocator_.clear();
    }

    virtual void create_and_prune_block_history(uint64_t) const override{

    };

    [[nodiscard]] bytes32_t state_root()
    {
        return {};
    }
};

MONAD_DB_NAMESPACE_END
