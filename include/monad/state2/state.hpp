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
#include <monad/state2/substate.hpp>

#include <ethash/keccak.hpp>

#include <quill/Quill.h>

MONAD_NAMESPACE_BEGIN

class State : public Substate
{
    std::optional<Account> &read_account(Address const &);

    Delta<bytes32_t> &
    read_storage_delta(Address const &, bytes32_t const &location);

    evmc_storage_status zero_out_key(Delta<bytes32_t> &delta)
    {
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

    evmc_storage_status
    set_current_value(Delta<bytes32_t> &delta, bytes32_t const &value) noexcept
    {
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

public:
    BlockState &block_state_;
    StateDeltas state_;
    Code code_;

    explicit State(BlockState &block_state)
        : Substate{}
        , block_state_{block_state}
        , state_{}
        , code_{}
    {
    }

    State(State &&) = default;
    State(State const &) = default;

    State &operator=(State &&other)
    {
        MONAD_DEBUG_ASSERT(&block_state_ == &other.block_state_);

        Substate::operator=(other);
        state_ = std::move(other.state_);
        code_ = std::move(other.code_);

        return *this;
    }

    State &operator=(State const &other)
    {
        MONAD_DEBUG_ASSERT(&block_state_ == &other.block_state_);

        Substate::operator=(other);
        state_ = other.state_;
        code_ = other.code_;

        return *this;
    }

    // EVMC Host Interface
    bool account_exists(Address const &address)
    {
        LOG_TRACE_L1("account_exists: {}", address);

        auto const &account = read_account(address);

        return account.has_value();
    };

    void create_contract(Address const &address)
    {
        LOG_TRACE_L1("create_contract: {}", address);

        auto &account = read_account(address);
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
    bytes32_t get_balance(Address const &address)
    {
        LOG_TRACE_L1("get_balance: {}", address);

        auto const &account = read_account(address);
        if (MONAD_LIKELY(account.has_value())) {
            return intx::be::store<bytes32_t>(account.value().balance);
        }
        return bytes32_t{0u};
    }

    void add_to_balance(Address const &address, uint256_t const &delta) noexcept
    {
        auto &account = read_account(address);
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
        Address const &address, uint256_t const &delta) noexcept
    {
        auto &account = read_account(address);
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

    uint64_t get_nonce(Address const &address) noexcept
    {
        LOG_TRACE_L1("get_nonce: {}", address);

        auto const &account = read_account(address);
        if (MONAD_LIKELY(account.has_value())) {
            return account.value().nonce;
        }
        return 0u;
    }

    void set_nonce(Address const &address, uint64_t const nonce)
    {
        LOG_TRACE_L1("set_nonce: {} = {}", address, nonce);

        auto &account = read_account(address);
        if (MONAD_UNLIKELY(!account.has_value())) {
            account = Account{};
        }
        account.value().nonce = nonce;
    }

    // EVMC Host Interface
    bytes32_t get_code_hash(Address const &address)
    {
        LOG_TRACE_L1("get_code_hash: {}", address);

        auto const &account = read_account(address);
        if (MONAD_LIKELY(account.has_value())) {
            return account.value().code_hash;
        }
        return NULL_HASH;
    }

    void set_code_hash(Address const &address, bytes32_t const &hash)
    {
        LOG_TRACE_L1("set_code_hash: {} = {}", address, hash);

        auto &account = read_account(address);
        MONAD_DEBUG_ASSERT(account.has_value());
        account.value().code_hash = hash;
    }

    // EVMC Host Interface
    bool
    selfdestruct(Address const &address, Address const &beneficiary) noexcept
    {
        LOG_TRACE_L1("selfdestruct: {}, {}", address, beneficiary);

        auto &account = read_account(address);
        MONAD_DEBUG_ASSERT(account.has_value());

        add_to_balance(beneficiary, account->balance);
        account->balance = 0;

        return Substate::selfdestruct(address);
    }

    void destruct_suicides() noexcept
    {
        LOG_TRACE_L1("destruct_suicides");

        for (auto const &address : destructed()) {
            auto &account = read_account(address);
            MONAD_DEBUG_ASSERT(account.has_value());
            account.reset();
        }
    }

    void destruct_touched_dead() noexcept
    {
        LOG_TRACE_L1("destruct_touched_dead");

        for (auto const &address : touched()) {
            auto &account = read_account(address);
            if (account.has_value() && account.value() == Account{}) {
                account.reset();
            }
        }
    }

    bool account_is_dead(Address const &address) noexcept
    {
        auto const &account = read_account(address);
        return !account.has_value() ||
               (account->balance == 0 && account->code_hash == NULL_HASH &&
                account->nonce == 0);
    }

    // EVMC Host Interface
    bytes32_t get_storage(Address const &address, bytes32_t const &key) noexcept
    {
        LOG_TRACE_L1("get_storage: {}, {}", address, key);

        return read_storage_delta(address, key).second;
    }

    // EVMC Host Interface
    evmc_storage_status set_storage(
        Address const &address, bytes32_t const &key,
        bytes32_t const &value) noexcept
    {
        LOG_TRACE_L1("set_storage: {}, {} = {}", address, key, value);

        auto &delta = read_storage_delta(address, key);
        if (value == bytes32_t{}) {
            return zero_out_key(delta);
        }
        return set_current_value(delta, value);
    }

    // EVMC Host Interface
    size_t get_code_size(Address const &address) noexcept
    {
        LOG_TRACE_L1("get_code_size: {}", address);

        auto const &account = read_account(address);
        if (MONAD_LIKELY(account.has_value())) {
            return read_code(account->code_hash, code_, block_state_).size();
        }
        return 0u;
    }

    // EVMC Host Interface
    size_t copy_code(
        Address const &address, size_t const offset, uint8_t *const buffer,
        size_t const buffer_size) noexcept
    {
        auto const &account = read_account(address);
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

    byte_string get_code(Address const &address) noexcept
    {
        LOG_TRACE_L1("get_code: {}", address);

        auto const &account = read_account(address);
        if (MONAD_LIKELY(account.has_value())) {
            return read_code(account->code_hash, code_, block_state_);
        }
        return {};
    }

    void set_code(Address const &address, byte_string const &code)
    {
        LOG_TRACE_L1("set_code: {} = {}", address, evmc::hex(code));

        auto const code_hash = std::bit_cast<monad::bytes32_t const>(
            ethash::keccak256(code.data(), code.size()));

        auto &account = read_account(address);
        if (MONAD_LIKELY(account.has_value())) {
            account->code_hash = code_hash;
            if (!code.empty()) {
                read_code(account->code_hash, code_, block_state_) = code;
            }
        }
    }

    void log_debug() const;
};

MONAD_NAMESPACE_END
