#pragma once

#include <monad/config.hpp>
#include <monad/core/account.hpp>
#include <monad/core/account_fmt.hpp>
#include <monad/core/address.hpp>
#include <monad/core/address_fmt.hpp>
#include <monad/core/assert.h>
#include <monad/core/bytes.hpp>
#include <monad/core/bytes_fmt.hpp>
#include <monad/core/int.hpp>
#include <monad/core/int_fmt.hpp>
#include <monad/core/likely.h>
#include <monad/core/receipt.hpp>

#include <monad/state2/block_state.hpp>
#include <monad/state2/block_state_ops.hpp>

#include <ankerl/unordered_dense.h>

#include <ethash/keccak.hpp>
#include <quill/Quill.h>

MONAD_NAMESPACE_BEGIN

struct State
{
    BlockState &block_state_;
    StateDeltas state_;
    Code code_;
    ankerl::unordered_dense::set<address_t> touched_;
    ankerl::unordered_dense::set<address_t> accessed_;
    ankerl::unordered_dense::map<
        address_t, ankerl::unordered_dense::set<bytes32_t>>
        accessed_storage_;
    ankerl::unordered_dense::set<address_t> destructed_;
    std::vector<Receipt::Log> logs_;

    explicit State(BlockState &block_state)
        : block_state_{block_state}
        , state_{}
        , code_{}
        , touched_{}
        , accessed_{}
        , accessed_storage_{}
        , logs_{}
    {
    }

    // EVMC Host Interface
    evmc_access_status access_account(address_t const &address)
    {
        LOG_TRACE_L1("access_account: {}", address);

        auto const [_, inserted] = accessed_.insert(address);
        if (inserted) {
            return EVMC_ACCESS_COLD;
        }
        return EVMC_ACCESS_WARM;
    }

    // EVMC Host Interface
    [[nodiscard]] bool account_exists(address_t const &address)
    {
        LOG_TRACE_L1("account_exists: {}", address);

        auto const &account = read_account(address, state_, block_state_);

        return account.has_value();
    };

    void create_contract(address_t const &address)
    {
        LOG_TRACE_L1("create_contract: {}", address);

        auto &account = read_account(address, state_, block_state_);
        if (MONAD_UNLIKELY(account.has_value())) {
            // eip-684: nonce should be zero and code should be empty
            MONAD_DEBUG_ASSERT(account->nonce == 0);
            MONAD_DEBUG_ASSERT(account->code_hash == NULL_HASH);
            // Keep the balance, per chapter 7 of the YP
        }
        else {
            account = Account{};
        }
    }

    // EVMC Host Interface
    [[nodiscard]] bytes32_t get_balance(address_t const &address)
    {
        LOG_TRACE_L1("get_balance: {}", address);

        auto const &account = read_account(address, state_, block_state_);
        if (MONAD_LIKELY(account.has_value())) {
            return intx::be::store<bytes32_t>(account.value().balance);
        }
        return bytes32_t{0u};
    }

    void
    add_to_balance(address_t const &address, uint256_t const &delta) noexcept
    {
        auto &account = read_account(address, state_, block_state_);
        if (MONAD_UNLIKELY(!account.has_value())) {
            account = Account{};
        }

        MONAD_DEBUG_ASSERT(
            std::numeric_limits<uint256_t>::max() - delta >=
            account.value().balance);

        LOG_TRACE_L1(
            "add_to_balance {} = {} + {}",
            address,
            account.value().balance,
            delta);

        account.value().balance += delta;
        touch(address);
    }

    void subtract_from_balance(
        address_t const &address, uint256_t const &delta) noexcept
    {
        auto &account = read_account(address, state_, block_state_);
        if (MONAD_UNLIKELY(!account.has_value())) {
            account = Account{};
        }

        MONAD_DEBUG_ASSERT(delta <= account.value().balance);

        LOG_TRACE_L1(
            "subtract_from_balance {} = {} - {}",
            address,
            account.value().balance,
            delta);

        account.value().balance -= delta;
        touch(address);
    }

    [[nodiscard]] uint64_t get_nonce(address_t const &address) noexcept
    {
        LOG_TRACE_L1("get_nonce: {}", address);

        auto const &account = read_account(address, state_, block_state_);
        if (MONAD_LIKELY(account.has_value())) {
            return account.value().nonce;
        }
        return 0u;
    }

    void set_nonce(address_t const &address, uint64_t const nonce)
    {
        LOG_TRACE_L1("set_nonce: {} = {}", address, nonce);

        auto &account = read_account(address, state_, block_state_);
        if (MONAD_UNLIKELY(!account.has_value())) {
            account = Account{};
        }
        account.value().nonce = nonce;
    }

    // EVMC Host Interface
    [[nodiscard]] bytes32_t get_code_hash(address_t const &address)
    {
        LOG_TRACE_L1("get_code_hash: {}", address);

        auto const &account = read_account(address, state_, block_state_);
        if (MONAD_LIKELY(account.has_value())) {
            return account.value().code_hash;
        }
        return NULL_HASH;
    }

    void set_code_hash(address_t const &address, bytes32_t const &hash)
    {
        LOG_TRACE_L1("set_code_hash: {} = {}", address, hash);

        auto &account = read_account(address, state_, block_state_);
        MONAD_DEBUG_ASSERT(account.has_value());
        account.value().code_hash = hash;
    }

    // EVMC Host Interface
    [[nodiscard]] bool selfdestruct(
        address_t const &address, address_t const &beneficiary) noexcept
    {
        LOG_TRACE_L1("selfdestruct: {}, {}", address, beneficiary);

        auto &account = read_account(address, state_, block_state_);
        MONAD_DEBUG_ASSERT(account.has_value());

        add_to_balance(beneficiary, account->balance);
        account->balance = 0;
        return destructed_.insert(address).second;
    }

    void destruct_suicides() noexcept
    {
        LOG_TRACE_L1("destruct_suicides");

        for (auto const &address : destructed_) {
            auto &account = read_account(address, state_, block_state_);
            MONAD_DEBUG_ASSERT(account.has_value());
            account.reset();
        }
    }

    void destruct_touched_dead() noexcept
    {
        LOG_TRACE_L1("destruct_touched_dead");

        for (auto const &touched : touched_) {
            auto &account = read_account(touched, state_, block_state_);
            if (account.has_value() && account.value() == Account{}) {
                account.reset();
            }
        }
    }

    [[nodiscard]] bool account_is_dead(address_t const &address) noexcept
    {
        auto const &account = read_account(address, state_, block_state_);
        return !account.has_value() ||
               (account->balance == 0 && account->code_hash == NULL_HASH &&
                account->nonce == 0);
    }

    // EVMC Host Interface
    evmc_access_status
    access_storage(address_t const &address, bytes32_t const &key) noexcept
    {
        LOG_TRACE_L1("access_storage: {}, {}", address, key);

        auto const &[_, inserted] = accessed_storage_[address].insert(key);
        if (inserted) {
            return EVMC_ACCESS_COLD;
        }
        return EVMC_ACCESS_WARM;
    }

    // EVMC Host Interface
    [[nodiscard]] bytes32_t
    get_storage(address_t const &address, bytes32_t const &key) noexcept
    {
        LOG_TRACE_L1("get_storage: {}, {}", address, key);

        return read_storage(address, 0u, key, state_, block_state_).second;
    }

    // EVMC Host Interface
    [[nodiscard]] evmc_storage_status set_storage(
        address_t const &address, bytes32_t const &key,
        bytes32_t const &value) noexcept
    {
        LOG_TRACE_L1("set_storage: {}, {} = {}", address, key, value);

        if (value == bytes32_t{}) {
            return zero_out_key(address, key);
        }
        return set_current_value(address, key, value);
    }

    [[nodiscard]] evmc_storage_status
    zero_out_key(address_t const &address, bytes32_t const &key) noexcept
    {
        auto &delta = read_storage(address, 0u, key, state_, block_state_);
        auto &status_value = delta.first;
        auto &current_value = delta.second;

        auto const status = [&] {
            if (current_value == bytes32_t{}) {
                return EVMC_STORAGE_ASSIGNED;
            }
            else if (status_value == current_value) {
                return EVMC_STORAGE_DELETED;
            }
            else if (status_value == bytes32_t{}) {
                return EVMC_STORAGE_ADDED_DELETED;
            }
            return EVMC_STORAGE_MODIFIED_DELETED;
        }();

        current_value = bytes32_t{};
        return status;
    }

    [[nodiscard]] evmc_storage_status set_current_value(
        address_t const &address, bytes32_t const &key,
        bytes32_t const &value) noexcept
    {
        auto &delta = read_storage(address, 0u, key, state_, block_state_);
        auto &status_value = delta.first;
        auto &current_value = delta.second;

        auto const status = [&] {
            if (current_value == bytes32_t{}) {
                if (status_value == bytes32_t{}) {
                    return EVMC_STORAGE_ADDED;
                }
                else if (value == status_value) {
                    return EVMC_STORAGE_DELETED_RESTORED;
                }
                return EVMC_STORAGE_DELETED_ADDED;
            }
            else if (status_value == current_value && status_value != value) {
                return EVMC_STORAGE_MODIFIED;
            }
            else if (status_value == value && status_value != current_value) {
                return EVMC_STORAGE_MODIFIED_RESTORED;
            }
            return EVMC_STORAGE_ASSIGNED;
        }();

        current_value = value;
        return status;
    }

    // EVMC Host Interface
    [[nodiscard]] size_t get_code_size(address_t const &address) noexcept
    {
        LOG_TRACE_L1("get_code_size: {}", address);

        auto const &account = read_account(address, state_, block_state_);
        if (MONAD_LIKELY(account.has_value())) {
            return read_code(account->code_hash, code_, block_state_).size();
        }
        return 0u;
    }

    // EVMC Host Interface
    [[nodiscard]] size_t copy_code(
        address_t const &address, size_t const offset, uint8_t *const buffer,
        size_t const buffer_size) noexcept
    {
        auto const &account = read_account(address, state_, block_state_);
        if (MONAD_LIKELY(account.has_value())) {
            auto const &code =
                read_code(account->code_hash, code_, block_state_);
            if (offset > code.size()) {
                return 0z;
            }
            auto const bytes_to_copy =
                std::min(code.size() - offset, buffer_size);
            std::copy_n(
                std::next(code.begin(), static_cast<long>(offset)),
                bytes_to_copy,
                buffer);
            return bytes_to_copy;
        }
        return 0z;
    }

    [[nodiscard]] byte_string get_code(address_t const &address) noexcept
    {
        LOG_TRACE_L1("get_code: {}", address);

        auto const &account = read_account(address, state_, block_state_);
        if (MONAD_LIKELY(account.has_value())) {
            return read_code(account->code_hash, code_, block_state_);
        }
        return {};
    }

    void set_code(address_t const &address, byte_string const &code)
    {
        LOG_TRACE_L1("set_code: {} = {}", address, evmc::hex(code));

        auto const code_hash = std::bit_cast<monad::bytes32_t const>(
            ethash::keccak256(code.data(), code.size()));

        auto &account = read_account(address, state_, block_state_);
        if (MONAD_LIKELY(account.has_value())) {
            account->code_hash = code_hash;
            if (!code.empty()) {
                read_code(account->code_hash, code_, block_state_) = code;
            }
        }
    }

    void store_log(Receipt::Log &&log)
    {
        logs_.emplace_back(log);
    }

    std::vector<Receipt::Log> &logs()
    {
        return logs_;
    }

    void warm_coinbase(address_t const &address) noexcept
    {
        accessed_.insert(address);
    }

    void touch(address_t const &address)
    {
        LOG_TRACE_L1("touched: {}", address);

        touched_.insert(address);
    }

    [[nodiscard]] constexpr bool is_touched(address_t const &address)
    {
        return touched_.contains(address);
    }

    void merge(State &new_state)
    {
        state_ = std::move(new_state.state_);
        code_ = std::move(new_state.code_);
        touched_ = std::move(new_state.touched_);
        accessed_ = std::move(new_state.accessed_);
        accessed_storage_ = std::move(new_state.accessed_storage_);
        destructed_ = std::move(new_state.destructed_);
        logs_ = std::move(new_state.logs_);
    }
};

MONAD_NAMESPACE_END
