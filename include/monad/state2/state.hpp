#pragma once

#include <monad/core/account.hpp>
#include <monad/core/address.hpp>
#include <monad/core/assert.h>
#include <monad/core/bytes.hpp>
#include <monad/core/likely.h>
#include <monad/core/receipt.hpp>

#include <monad/db/db.hpp>

#include <monad/logging/monad_log.hpp>

#include <monad/state/config.hpp>
#include <monad/state2/block_state.hpp>
#include <monad/state2/block_state_ops.hpp>
#include <monad/state2/state.hpp>

#include <ethash/keccak.hpp>

#include <unordered_map>
#include <unordered_set>

MONAD_STATE_NAMESPACE_BEGIN

// EVMC state object
template <class Mutex, class TBlockCache>
struct State
{
    BlockState<Mutex> &bs;
    Db &db;
    TBlockCache &block_cache_;
    StateDeltas s;
    Code code_;
    std::unordered_set<address_t> accessed_;
    std::unordered_map<address_t, std::unordered_set<bytes32_t>>
        accessed_storage_{};
    unsigned total_selfdestructs_;
    uint256_t gas_award_;
    std::vector<Receipt::Log> logs_;

    decltype(monad::log::logger_t::get_logger()) logger =
        monad::log::logger_t::get_logger("state_logger");

    explicit State(BlockState<Mutex> &b, Db &d, TBlockCache &cache)
        : bs{b}
        , db{d}
        , block_cache_{cache}
        , s{}
        , code_{}
        , accessed_{}
        , accessed_storage_{}
        , total_selfdestructs_{}
        , gas_award_{}
        , logs_{}
    {
    }

    // EVMC Host Interface
    evmc_access_status access_account(address_t const &address)
    {
        MONAD_LOG_DEBUG(logger, "access_account: {}", address);

        auto const [_, inserted] = accessed_.insert(address);
        if (inserted) {
            return EVMC_ACCESS_COLD;
        }
        return EVMC_ACCESS_WARM;
    }

    // EVMC Host Interface
    [[nodiscard]] bool account_exists(address_t const &address)
    {
        MONAD_LOG_DEBUG(logger, "account_exists: {}", address);

        auto const account = read_account<Mutex>(address, s, bs, db);

        return account.has_value();
    };

    void create_account(address_t const &address)
    {
        MONAD_LOG_DEBUG(logger, "create_account: {}", address);

        auto &account = read_account<Mutex>(address, s, bs, db);
        account = Account{};
    }

    // EVMC Host Interface
    [[nodiscard]] bytes32_t get_balance(address_t const &address)
    {
        auto const account = read_account<Mutex>(address, s, bs, db);
        if (MONAD_LIKELY(account.has_value())) {
            return intx::be::store<bytes32_t>(account.value().balance);
        }
        return bytes32_t{0u};
    }

    void set_balance(address_t const &address, uint256_t new_balance) noexcept
    {
        auto &account = read_account<Mutex>(address, s, bs, db);
        MONAD_DEBUG_ASSERT(account.has_value());

        auto const previous_balance = account.value().balance;
        MONAD_LOG_DEBUG(
            logger,
            "set_balance: {} = {}, ({}{})",
            address,
            intx::to_string(new_balance, 16),
            new_balance >= previous_balance ? "+" : "-",
            new_balance >= previous_balance
                ? intx::to_string(new_balance - previous_balance, 16)
                : intx::to_string(previous_balance - new_balance, 16));

        account.value().balance = new_balance;
    }

    [[nodiscard]] uint64_t get_nonce(address_t const &address) noexcept
    {
        MONAD_LOG_DEBUG(logger, "get_nonce: {}", address);

        auto const account = read_account<Mutex>(address, s, bs, db);
        if (MONAD_LIKELY(account.has_value())) {
            return account.value().nonce;
        }
        return 0u;
    }

    void set_nonce(address_t const &address, uint64_t nonce)
    {
        MONAD_LOG_DEBUG(logger, "set_nonce: {} = {}", address, nonce);

        auto &account = read_account<Mutex>(address, s, bs, db);
        MONAD_DEBUG_ASSERT(account.has_value());
        account.value().nonce = nonce;
    }

    // EVMC Host Interface
    [[nodiscard]] bytes32_t get_code_hash(address_t const &address)
    {
        MONAD_LOG_DEBUG(logger, "get_code_hash: {}", address);

        auto const account = read_account<Mutex>(address, s, bs, db);
        if (MONAD_LIKELY(account.has_value())) {
            return account.value().code_hash;
        }
        return NULL_HASH;
    }

    void set_code_hash(address_t const &address, bytes32_t const &hash)
    {
        auto &account = read_account<Mutex>(address, s, bs, db);
        MONAD_DEBUG_ASSERT(account.has_value());
        account.value().code_hash = hash;
    }

    // EVMC Host Interface
    [[nodiscard]] bool
    selfdestruct(address_t const &address, address_t const &b) noexcept
    {
        MONAD_LOG_DEBUG(logger, "selfdestruct: {}, {}", address, b);

        auto &account = read_account<Mutex>(address, s, bs, db);
        auto &beneficiary = read_account<Mutex>(b, s, bs, db);

        if (account.has_value()) {
            if (!beneficiary.has_value()) {
                create_account(b);
            }

            auto total = account.value().balance + beneficiary.value().balance;
            account.reset();
            set_balance(b, total);
            ++total_selfdestructs_;
            return true;
        }
        return false;
    }

    [[nodiscard]] unsigned total_selfdestructs() const noexcept
    {
        return total_selfdestructs_;
    }

    void destruct_suicides() const noexcept {}

    void destruct_touched_dead() noexcept
    {
        MONAD_LOG_DEBUG(logger, "{}", "destruct_touched_dead");

        for (auto &it : s) {
            if (it.second.account.second.has_value() &&
                it.second.account.second.value() == Account{})
                it.second.account.second.reset();
        }
    }

    // EVMC Host Interface
    evmc_access_status
    access_storage(address_t const &address, bytes32_t const &key) noexcept
    {
        MONAD_LOG_DEBUG(logger, "access_storage: {}, {}", address, key);

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
        MONAD_LOG_DEBUG(logger, "get_storage: {}, {}", address, key);

        return read_storage<Mutex>(address, 0u, key, s, bs, db).second;
    }

    // EVMC Host Interface
    [[nodiscard]] evmc_storage_status set_storage(
        address_t const &address, bytes32_t const &key,
        bytes32_t const &value) noexcept
    {
        MONAD_LOG_DEBUG(
            logger, "set_storage: {}, {} = {}", address, key, value);

        if (value == bytes32_t{}) {
            return zero_out_key(address, key);
        }
        return set_current_value(address, key, value);
    }

    [[nodiscard]] evmc_storage_status
    zero_out_key(address_t const &a, bytes32_t const &key) noexcept
    {
        auto &delta = read_storage<Mutex>(a, 0u, key, s, bs, db);
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
        address_t const &a, bytes32_t const &key,
        bytes32_t const &value) noexcept
    {
        auto &delta = read_storage<Mutex>(a, 0u, key, s, bs, db);
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
        auto const &account = read_account<Mutex>(address, s, bs, db);
        if (account.has_value()) {
            return read_code<Mutex>(account->code_hash, code_, bs, db).size();
        }
        return 0u;
    }

    // EVMC Host Interface
    [[nodiscard]] size_t copy_code(
        address_t const &address, size_t offset, uint8_t *buffer,
        size_t buffer_size) noexcept
    {
        auto const &account = read_account<Mutex>(address, s, bs, db);
        if (MONAD_LIKELY(account.has_value())) {
            auto const &code =
                read_code<Mutex>(account->code_hash, code_, bs, db);
            auto const bytes_to_copy =
                std::min(code.size() - offset, buffer_size);
            std::copy_n(
                std::next(code.begin(), static_cast<long>(offset)),
                bytes_to_copy,
                buffer);
            return bytes_to_copy;
        }
        return 0u;
    }

    [[nodiscard]] byte_string get_code(address_t const address) noexcept
    {
        auto const account = read_account<Mutex>(address, s, bs, db);
        if (MONAD_LIKELY(account.has_value())) {
            return read_code<Mutex>(account->code_hash, code_, bs, db);
        }
        return {};
    }

    void set_code(address_t const &address, byte_string const &code)
    {
        MONAD_LOG_DEBUG(logger, "set_code: {} = {}", address, evmc::hex(code));

        auto const code_hash = std::bit_cast<monad::bytes32_t const>(
            ethash::keccak256(code.data(), code.size()));

        auto &account = read_account<Mutex>(address, s, bs, db);
        if (MONAD_LIKELY(account.has_value())) {
            account->code_hash = code_hash;
            if (!code.empty()) {
                read_code<Mutex>(account->code_hash, code_, bs, db) = code;
            }
        }
    }

    // EVMC Host Interface
    [[nodiscard]] bytes32_t get_block_hash(int64_t number) const noexcept
    {
        MONAD_DEBUG_ASSERT(number > 0);
        return block_cache_.get_block_hash(static_cast<uint64_t>(number));
    }

    void store_log(Receipt::Log &&l) { logs_.emplace_back(l); }

    std::vector<Receipt::Log> &logs() { return logs_; }

    void warm_coinbase(address_t const &a) noexcept { accessed_.insert(a); }

    void add_txn_award(uint256_t const &reward)
    {
        MONAD_LOG_DEBUG(logger, "add_txn_award: {}", reward);
        gas_award_ += reward;
    }

    [[nodiscard]] constexpr uint256_t const &gas_award() const
    {
        return gas_award_;
    }

    void apply_reward(address_t const &a, uint256_t const &r)
    {
        MONAD_LOG_DEBUG(logger, "apply_award: {}", r);

        auto &account = read_account(a, s, bs, db);

        if (!account.has_value()) {
            create_account(a);
        }

        account.value().balance += r;
    }

    void merge(State &new_state)
    {
        s = std::move(new_state.s);
        code_ = std::move(new_state.code_);
        accessed_ = std::move(new_state.accessed_);
        accessed_storage_ = std::move(new_state.accessed_storage_);
        total_selfdestructs_ = new_state.total_selfdestructs_;
        gas_award_ = new_state.gas_award_;
        logs_ = std::move(new_state.logs_);
    }
};

MONAD_STATE_NAMESPACE_END
