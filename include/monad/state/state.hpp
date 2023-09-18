#pragma once

#include <monad/core/account.hpp>
#include <monad/core/address.hpp>
#include <monad/core/bytes.hpp>
#include <monad/core/int.hpp>
#include <monad/core/receipt.hpp>

#include <monad/state/config.hpp>
#include <monad/state/state_changes.hpp>

#include <monad/logging/formatter.hpp>

#include <ethash/keccak.hpp>
#include <quill/Quill.h>

#include <bit>
#include <vector>

MONAD_STATE_NAMESPACE_BEGIN

template <
    class TAccountState, class TValueState, class TCodeState, class TBlockCache,
    class TDatabase>
struct State
{
    struct ChangeSet
    {
        uint256_t gas_award_{};
        typename TAccountState::ChangeSet accounts_;
        typename TValueState::ChangeSet storage_;
        typename TCodeState::ChangeSet code_;
        std::vector<Receipt::Log> logs_{};
        TBlockCache &block_cache_{};
        unsigned int txn_id_{};

        ChangeSet(
            unsigned int i, typename TAccountState::ChangeSet &&a,
            typename TValueState::ChangeSet &&s,
            typename TCodeState::ChangeSet &&c, TBlockCache &b)
            : accounts_{std::move(a)}
            , storage_{std::move(s)}
            , code_{std::move(c)}
            , block_cache_{b}
            , txn_id_{i}
        {
        }

        void add_txn_award(uint256_t const &a)
        {
            LOG_DEBUG("add_txn_award: {}", a);
            gas_award_ += a;
        }

        unsigned int txn_id() const noexcept { return txn_id_; }
        void create_account(address_t const &a) noexcept
        {
            LOG_DEBUG("create_account: {}", a);
            accounts_.create_account(a);
        }

        // EVMC Host Interface
        [[nodiscard]] bool account_exists(address_t const &a) const
        {
            LOG_DEBUG("account_exists: {}", a);
            return accounts_.account_exists(a);
        }

        // EVMC Host Interface
        evmc_access_status access_account(address_t const &a) noexcept
        {
            LOG_DEBUG("access_account: {}", a);
            return accounts_.access_account(a);
        }

        // EVMC Host Interface
        [[nodiscard]] bytes32_t get_balance(address_t const &a) const noexcept
        {
            return accounts_.get_balance(a);
        }

        void set_balance(address_t const &a, uint256_t const &new_balance)
        {
            [[maybe_unused]] auto const previous_balance =
                intx::be::load<monad::uint256_t>(get_balance(a));

            LOG_DEBUG(
                "set_balance: {} = {}, ({}{})",
                a,
                intx::to_string(new_balance, 16),
                new_balance >= previous_balance ? "+" : "-",
                new_balance >= previous_balance
                    ? intx::to_string(new_balance - previous_balance, 16)
                    : intx::to_string(previous_balance - new_balance, 16));
            accounts_.set_balance(a, new_balance);
        }

        [[nodiscard]] auto get_nonce(address_t const &a) const noexcept
        {
            LOG_DEBUG("get_nonce: {}", a);
            return accounts_.get_nonce(a);
        }

        void set_nonce(address_t const &a, uint64_t nonce) noexcept
        {
            LOG_DEBUG("set_nonce: {} = {}", a, nonce);
            accounts_.set_nonce(a, nonce);
        }

        // EVMC Host Interface
        [[nodiscard]] bytes32_t get_code_hash(address_t const &a) const noexcept
        {
            LOG_DEBUG("get_code_hash: {}", a);
            return accounts_.get_code_hash(a);
        }

        [[nodiscard]] bool selfdestruct(address_t const &a, address_t const &b)
        {
            LOG_DEBUG("selfdestruct: {}, {}", a, b);
            return accounts_.selfdestruct(a, b);
        }

        void destruct_suicides()
        {
            LOG_DEBUG("{}", "destruct_suicides");
            accounts_.destruct_suicides();
        }

        void destruct_touched_dead()
        {
            LOG_DEBUG("{}", "destruct_touched_dead");
            accounts_.destruct_touched_dead();
        }

        uint64_t total_selfdestructs() const noexcept
        {
            return accounts_.total_selfdestructs();
        }

        // EVMC Host Interface
        evmc_access_status
        access_storage(address_t const &a, bytes32_t const &key)
        {
            LOG_DEBUG("access_storage: {}, {}", a, key);
            return storage_.access_storage(a, key);
        }

        // EVMC Host Interface
        [[nodiscard]] bytes32_t
        get_storage(address_t const &a, bytes32_t const &key) const noexcept
        {
            LOG_DEBUG("get_storage: {}, {}", a, key);
            return storage_.get_storage(a, key);
        }

        // EVMC Host Interface
        [[nodiscard]] evmc_storage_status set_storage(
            address_t const &a, bytes32_t const &key, bytes32_t const &value)
        {
            LOG_DEBUG("set_storage: {}, {} = {}", a, key, value);
            return storage_.set_storage(a, key, value);
        }

        // Account contract accesses
        void set_code(address_t const &a, byte_string const &c)
        {
            LOG_DEBUG("set_code: {} = {}", a, evmc::hex(c));
            auto const code_hash = std::bit_cast<monad::bytes32_t const>(
                ethash::keccak256(c.data(), c.size()));

            code_.set_code(code_hash, c);
            accounts_.set_code_hash(a, code_hash);
        }

        // EVMC Host Interface
        [[nodiscard]] size_t get_code_size(address_t const &a) const noexcept
        {
            return code_.get_code_size(get_code_hash(a));
        }

        // EVMC Host Interface
        [[nodiscard]] size_t copy_code(
            address_t const &a, size_t offset, uint8_t *buffer,
            size_t size) const noexcept
        {
            return code_.copy_code(get_code_hash(a), offset, buffer, size);
        }

        [[nodiscard]] byte_string get_code(bytes32_t const &b) const noexcept
        {
            return code_.code_at(b);
        }

        void revert() noexcept
        {
            LOG_DEBUG("{}", "revert");
            accounts_.revert();
            storage_.revert();
            code_.revert();
        }

        [[nodiscard]] bytes32_t get_block_hash(int64_t number) const noexcept
        {
            MONAD_DEBUG_ASSERT(number > 0);
            return block_cache_.get_block_hash(static_cast<uint64_t>(number));
        }

        // Logs
        void store_log(Receipt::Log &&l) { logs_.emplace_back(l); }

        std::vector<Receipt::Log> &logs() { return logs_; }

        void warm_coinbase(address_t const &beneficiary)
        {
            accounts_.warm_coinbase(beneficiary);
        }
    };

    enum class MergeStatus
    {
        WILL_SUCCEED,
        TRY_LATER,
        COLLISION_DETECTED,
    };

    uint256_t gas_award_{};
    TAccountState &accounts_;
    TValueState &storage_;
    TCodeState &code_;
    TBlockCache &block_cache_{};
    TDatabase &db_{};
    unsigned int current_txn_{};

    State(
        TAccountState &a, TValueState &s, TCodeState &c, TBlockCache &bc,
        TDatabase &db)
        : accounts_{a}
        , storage_{s}
        , code_{c}
        , block_cache_{bc}
        , db_{db}
    {
    }

    void apply_reward(address_t const &a, uint256_t const &reward)
    {
        LOG_DEBUG("apply_reward {} {}", a, reward);
        accounts_.apply_reward(a, reward);
    }

    [[nodiscard]] constexpr uint256_t const &gas_award() const
    {
        return gas_award_;
    }

    unsigned int current_txn() const { return current_txn_; }

    ChangeSet get_new_changeset(unsigned int id) const
    {
        return ChangeSet(
            id,
            typename TAccountState::ChangeSet{accounts_},
            typename TValueState::ChangeSet{storage_},
            typename TCodeState::ChangeSet{code_},
            block_cache_);
    }

    MergeStatus can_merge_changes(ChangeSet const &c) const
    {
        if (current_txn() != c.txn_id()) {
            return MergeStatus::TRY_LATER;
        }

        if (accounts_.can_merge(c.accounts_) &&
            storage_.can_merge(c.storage_) && code_.can_merge(c.code_)) {
            return MergeStatus::WILL_SUCCEED;
        }
        return MergeStatus::COLLISION_DETECTED;
    }

    void merge_changes(ChangeSet &c)
    {
        LOG_DEBUG("Account Changeset: {}", c.accounts_.changed_);

        LOG_DEBUG("Storage Changeset: {}", c.storage_.touched_.storage_);

        LOG_DEBUG("Code Changeset: {}", c.code_.code_);

        accounts_.merge_changes(c.accounts_);
        storage_.merge_touched(c.storage_);
        code_.merge_changes(c.code_);
        gas_award_ += c.gas_award_;
        ++current_txn_;
    }

    bool can_commit() const
    {
        return accounts_.can_commit() && storage_.can_commit() &&
               code_.can_commit();
    }

    void commit()
    {
        db_.commit(StateChanges{
            .account_changes = accounts_.gather_changes(),
            .storage_changes = storage_.gather_changes(),
            .code_changes = code_.gather_changes()});
        accounts_.clear_changes();
        storage_.clear_changes();
        code_.clear_changes();
        current_txn_ = 0;
        gas_award_ = 0;
    }

    [[nodiscard]] bytes32_t get_state_hash() const
    {
        return accounts_.get_state_hash();
    }

    constexpr void create_and_prune_block_history(uint64_t block_number) const
    {
        db_.create_and_prune_block_history(block_number);
    }
};

MONAD_STATE_NAMESPACE_END
