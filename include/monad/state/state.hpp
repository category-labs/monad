#pragma once

#include <monad/core/account.hpp>
#include <monad/core/address.hpp>
#include <monad/core/bytes.hpp>
#include <monad/core/int.hpp>
#include <monad/core/receipt.hpp>

#include <monad/state/config.hpp>

#include <ethash/keccak.hpp>

#include <bit>
#include <vector>

MONAD_STATE_NAMESPACE_BEGIN

template <
    class TAccountState, class TValueState, class TCodeState, class TBlockCache>
struct State
{
    struct WorkingCopy
    {
        uint256_t gas_award_{};
        typename TAccountState::WorkingCopy accounts_;
        typename TValueState::WorkingCopy storage_;
        typename TCodeState::WorkingCopy code_;
        std::vector<Receipt::Log> logs_{};
        TBlockCache &block_cache_{};
        unsigned int txn_id_{};

        WorkingCopy(
            unsigned int i, typename TAccountState::WorkingCopy &&a,
            typename TValueState::WorkingCopy &&s,
            typename TCodeState::WorkingCopy &&c, TBlockCache &b)
            : accounts_{std::move(a)}
            , storage_{std::move(s)}
            , code_{std::move(c)}
            , block_cache_{b}
            , txn_id_{i}
        {
        }

        void add_txn_award(uint256_t const &a) { gas_award_ += a; }

        unsigned int txn_id() const noexcept { return txn_id_; }
        void create_account(address_t const &a) noexcept
        {
            accounts_.create_account(a);
        }

        // EVMC Host Interface
        [[nodiscard]] bool account_exists(address_t const &a) const
        {
            return accounts_.account_exists(a);
        }

        // EVMC Host Interface
        evmc_access_status access_account(address_t const &a) noexcept
        {
            return accounts_.access_account(a);
        }

        // EVMC Host Interface
        [[nodiscard]] bytes32_t get_balance(address_t const &a) const noexcept
        {
            return accounts_.get_balance(a);
        }

        void set_balance(address_t const &a, uint256_t const &b)
        {
            accounts_.set_balance(a, b);
        }

        [[nodiscard]] auto get_nonce(address_t const &a) const noexcept
        {
            return accounts_.get_nonce(a);
        }

        void set_nonce(address_t const &a, uint64_t nonce) noexcept
        {
            accounts_.set_nonce(a, nonce);
        }

        // EVMC Host Interface
        [[nodiscard]] bytes32_t get_code_hash(address_t const &a) const noexcept
        {
            return accounts_.get_code_hash(a);
        }

        [[nodiscard]] bool selfdestruct(address_t const &a, address_t const &b)
        {
            return accounts_.selfdestruct(a, b);
        }

        void destruct_suicides() { accounts_.destruct_suicides(); }

        void destruct_touched_dead() { accounts_.destruct_touched_dead(); }

        uint64_t total_selfdestructs() const noexcept
        {
            return accounts_.total_selfdestructs();
        }

        // EVMC Host Interface
        evmc_access_status
        access_storage(address_t const &a, bytes32_t const &key)
        {
            return storage_.access_storage(a, key);
        }

        // EVMC Host Interface
        [[nodiscard]] bytes32_t
        get_storage(address_t const &a, bytes32_t const &key) const noexcept
        {
            return storage_.get_storage(a, key);
        }

        // EVMC Host Interface
        [[nodiscard]] evmc_storage_status set_storage(
            address_t const &a, bytes32_t const &key, bytes32_t const &value)
        {
            return storage_.set_storage(a, key, value);
        }

        // Account contract accesses
        void set_code(address_t const &a, byte_string const &c)
        {
            auto const code_hash = std::bit_cast<const monad::bytes32_t>(
                ethash::keccak256(c.data(), c.size()));

            code_.set_code(a, c);
            accounts_.set_code_hash(a, code_hash);
        }

        // EVMC Host Interface
        [[nodiscard]] size_t get_code_size(address_t const &a) const noexcept
        {
            return code_.get_code_size(a);
        }

        // EVMC Host Interface
        [[nodiscard]] size_t copy_code(
            address_t const &a, size_t offset, uint8_t *buffer,
            size_t size) const noexcept
        {
            return code_.copy_code(a, offset, buffer, size);
        }

        [[nodiscard]] byte_string_view
        get_code(address_t const &a) const noexcept
        {
            return code_.code_at(a);
        }

        void revert() noexcept
        {
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
    unsigned int current_txn_{};

    State(TAccountState &a, TValueState &s, TCodeState &c, TBlockCache &bc)
        : accounts_{a}
        , storage_{s}
        , code_{c}
        , block_cache_{bc}
    {
    }

    void apply_block_reward(address_t const &a, uint256_t const &reward)
    {
        accounts_.apply_reward(a, reward + gas_award_);
    }

    void apply_ommer_reward(address_t const &a, uint256_t const &reward)
    {
        accounts_.apply_reward(a, reward);
    }

    unsigned int current_txn() const { return current_txn_; }

    WorkingCopy get_working_copy(unsigned int id) const
    {
        return WorkingCopy(
            id,
            typename TAccountState::WorkingCopy{accounts_},
            typename TValueState::WorkingCopy{storage_},
            typename TCodeState::WorkingCopy{code_},
            block_cache_);
    }

    MergeStatus can_merge_changes(WorkingCopy const &c) const
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

    void merge_changes(WorkingCopy &c)
    {
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
        // Note: storage updates must be committed prior to the account
        // updates, since each account needs the most up-to-date storage
        // root
        storage_.commit_all_merged();
        accounts_.commit_all_merged();
        code_.commit_all_merged();
        current_txn_ = 0;
        gas_award_ = 0;
    }

    [[nodiscard]] bytes32_t get_state_hash() const
    {
        return accounts_.get_state_hash();
    }
};

MONAD_STATE_NAMESPACE_END
