#pragma once

#include <monad/config.hpp>
#include <monad/core/account.hpp>
#include <monad/core/address.hpp>
#include <monad/core/assert.h>
#include <monad/core/byte_string.hpp>
#include <monad/core/bytes.hpp>
#include <monad/core/fmt/address_fmt.hpp>
#include <monad/core/fmt/bytes_fmt.hpp>
#include <monad/core/fmt/int_fmt.hpp>
#include <monad/core/keccak.hpp>
#include <monad/core/receipt.hpp>
#include <monad/state2/block_state.hpp>
#include <monad/state3/account_state.hpp>
#include <monad/state3/version_stack.hpp>
#include <monad/synchronization/spin_lock.hpp>
#include <monad/types/incarnation.hpp>
#include <monad/vm/evmone/code_analysis.hpp>

#include <evmc/evmc.h>

#include <ankerl/unordered_dense.h>

#include <boost/fiber/future/promise.hpp>

#include <quill/detail/LogMacros.h>

#include <algorithm>
#include <bit>
#include <cstddef>
#include <cstdint>
#include <memory>
#include <optional>
#include <utility>

MONAD_NAMESPACE_BEGIN

class ReadSpeculation
{
    std::atomic<bool> found_value_{false};
    bool waiting_{false};
    uint32_t n_pending_{0};
    boost::fibers::promise<void> promise_;
    SpinLock lock_;

public:
    // Executed by tx fiber
    void pre_read()
    {
        MONAD_ASSERT(!waiting_);
        std::unique_lock l(lock_);
        ++n_pending_;
    }

    void await_reads()
    {
        bool wait = false;
        MONAD_ASSERT(!waiting_);
        {
            std::unique_lock l(lock_);
            if (n_pending_) {
                waiting_ = true;
                wait = true;
            }
        }
        if (wait) {
            promise_.get_future().get();
            std::unique_lock l(lock_);
        }
    }

    bool validate_reads()
    {
        await_reads();
        return !found_value_.load(std::memory_order_acquire);
    }

    // Executed by db thread
    void post_read(bool found_value)
    {
        if (found_value) {
            set_found_value();
        }
        std::unique_lock l(lock_);
        MONAD_ASSERT(n_pending_ > 0);
        if ((--n_pending_ == 0) && waiting_) {
            promise_.set_value();
        }
    }

    void set_found_value()
    {
        found_value_.store(true, std::memory_order_release);
    }
};

class State
{
    template <typename K, typename V>
    using Map = ankerl::unordered_dense::segmented_map<K, V>;

    BlockState &block_state_;

    Incarnation const incarnation_;

    Map<Address, AccountState> original_{};

    Map<Address, VersionStack<AccountState>> current_{};

    VersionStack<std::vector<Receipt::Log>> logs_{{}};

    Map<bytes32_t, std::shared_ptr<CodeAnalysis>> code_{};

    unsigned version_{0};

    bool relaxed_validation_{false};

    bool first_account_read_{true};
    bool use_read_speculation_{false};
    ReadSpeculation read_speculation_;

    bool use_read_speculation()
    {
        return use_read_speculation_;
    }

public:
    AccountState &original_account_state(Address const &address)
    {
        auto it = original_.find(address);
        if (it == original_.end()) {
            // block state
#if 1
            auto fn1 = [this] { read_speculation_.pre_read(); };
            auto fn2 = [this](bool hasval) {
                read_speculation_.post_read(hasval);
            };
            auto const account = [&] {
                if (use_read_speculation() && !first_account_read_) {
                    return block_state_.read_account(address, fn1, fn2);
                }
                else {
                    first_account_read_ = false;
                    return block_state_.read_account(address);
                }
            }();
#else
            auto const account = block_state_.read_account(address);
#endif
            it = original_.try_emplace(address, account).first;
        }
        return it->second;
    }

private:
    AccountState const &recent_account_state(Address const &address)
    {
        // current
        auto const it = current_.find(address);
        if (it != current_.end()) {
            return it->second.recent();
        }
        // original
        return original_account_state(address);
    }

    AccountState &current_account_state(Address const &address)
    {
        // current
        auto it = current_.find(address);
        if (MONAD_UNLIKELY(it == current_.end())) {
            // original
            auto const &account_state = original_account_state(address);
            it = current_.try_emplace(address, account_state, version_).first;
        }
        return it->second.current(version_);
    }

    std::optional<Account> &current_account(Address const &address)
    {
        return current_account_state(address).account_;
    }

    friend class BlockState; // TODO

public:
    State(BlockState &block_state, Incarnation const incarnation)
        : block_state_{block_state}
        , incarnation_{incarnation}
    {
    }

    State(State &&) = delete;
    State(State const &) = delete;
    State &operator=(State &&) = delete;
    State &operator=(State const &) = delete;

    void push()
    {
        ++version_;
    }

    void pop_accept()
    {
        MONAD_ASSERT(version_);

        for (auto it = current_.begin(); it != current_.end(); ++it) {
            it->second.pop_accept(version_);
        }

        logs_.pop_accept(version_);

        --version_;
    }

    void pop_reject()
    {
        MONAD_ASSERT(version_);

        std::vector<Address> removals;

        for (auto it = current_.begin(); it != current_.end(); ++it) {
            if (it->second.pop_reject(version_)) {
                removals.push_back(it->first);
            }
        }

        logs_.pop_reject(version_);

        while (removals.size()) {
            current_.erase(removals.back());
            removals.pop_back();
        }

        --version_;
    }

    [[nodiscard]] bool relaxed_validation() const
    {
        return relaxed_validation_;
    }

    void set_relaxed_validation()
    {
        relaxed_validation_ = true;
    }

    void set_read_speculation(bool value)
    {
        use_read_speculation_ = value;
    }

    bool validate_reads()
    {
        bool ret = read_speculation_.validate_reads();
        return ret;
    }

    ////////////////////////////////////////

    std::optional<Account> const &recent_account(Address const &address)
    {
        return recent_account_state(address).account_;
    }

    void set_original_nonce_and_balance(
        Address const &address, uint64_t const nonce,
        uint256_t const &min_balance)
    {
        auto &account_state = original_account_state(address);
        auto &account = account_state.account_;
        if (!account.has_value()) {
            account = Account{};
        }
        account->nonce = nonce;
        account_state.set_validate_exact_nonce();
        if (account->balance < min_balance) {
            account->balance = min_balance;
        }
        account_state.set_min_balance(min_balance);
    }

    ////////////////////////////////////////

    bool account_exists(Address const &address)
    {
        return recent_account(address).has_value();
    }

    bool account_is_dead(Address const &address)
    {
        return is_dead(recent_account(address));
    }

    uint64_t get_nonce(Address const &address)
    {
        auto const &account = recent_account(address);
        original_account_state(address).set_validate_exact_nonce();
        if (MONAD_LIKELY(account.has_value())) {
            return account.value().nonce;
        }
        return 0;
    }

    bytes32_t get_balance(Address const &address)
    {
        auto const &account = recent_account(address);
        if (MONAD_LIKELY(account.has_value())) {
            original_account_state(address).set_validate_exact_balance();
            return intx::be::store<bytes32_t>(account.value().balance);
        }
        return {};
    }

    bytes32_t get_code_hash(Address const &address)
    {
        auto const &account = recent_account(address);
        if (MONAD_LIKELY(account.has_value())) {
            return account.value().code_hash;
        }
        return NULL_HASH;
    }

    bytes32_t get_storage(Address const &address, bytes32_t const &key)
    {
        auto fn1 = [this] { read_speculation_.pre_read(); };
        auto fn2 = [this](bool hasval) { read_speculation_.post_read(hasval); };
        auto const it = current_.find(address);
        if (it == current_.end()) {
            auto const it2 = original_.find(address);
#if 1
            if (it2 == original_.end()) {
                // We must have guessed incorrectly that the account
                // has no value.
                read_speculation_.set_found_value();
                return bytes32_t{};
            }
#else
            MONAD_ASSERT(it2 != original_.end());
#endif
            auto &account_state = it2->second;
            auto const &account = account_state.account_;
            MONAD_ASSERT(account.has_value());
            auto &storage = account_state.storage_;
            auto it3 = storage.find(key);
            if (it3 == storage.end()) {
#if 1
                bytes32_t const value = [&] {
                    if (use_read_speculation()) {
                        return block_state_.read_storage(
                            address,
                            account.value().incarnation,
                            key,
                            fn1,
                            fn2);
                    }
                    else {
                        return block_state_.read_storage(
                            address, account.value().incarnation, key);
                    }
                }();
#else
                bytes32_t const value = block_state_.read_storage(
                    address, account.value().incarnation, key);
#endif
                it3 = storage.try_emplace(key, value).first;
            }
            return it3->second;
        }
        else {
            auto const &account_state = it->second.recent();
            auto const &account = account_state.account_;
            MONAD_ASSERT(account.has_value());
            auto const &storage = account_state.storage_;
            if (auto const it2 = storage.find(key); it2 != storage.end()) {
                return it2->second;
            }
            auto const it2 = original_.find(address);
            MONAD_ASSERT(it2 != original_.end());
            auto &original_account_state = it2->second;
            auto const &original_account = original_account_state.account_;
            if (!original_account.has_value() ||
                account.value().incarnation !=
                    original_account.value().incarnation) {
                return {};
            }
            auto &original_storage = original_account_state.storage_;
            auto it3 = original_storage.find(key);
            if (it3 == original_storage.end()) {
#if 1
                bytes32_t const value = [&] {
                    if (use_read_speculation()) {
                        return block_state_.read_storage(
                            address,
                            account.value().incarnation,
                            key,
                            fn1,
                            fn2);
                    }
                    else {
                        return block_state_.read_storage(
                            address, account.value().incarnation, key);
                    }
                }();
#else
                bytes32_t const value = block_state_.read_storage(
                    address, account.value().incarnation, key);
#endif
                it3 = original_storage.try_emplace(key, value).first;
            }
            return it3->second;
        }
    }

    bytes32_t
    get_transient_storage(Address const &address, bytes32_t const &key)
    {
        return recent_account_state(address).get_transient_storage(key);
    }

    bool is_touched(Address const &address)
    {
        auto const &account_state = recent_account_state(address);
        return account_state.is_touched();
    }

    ////////////////////////////////////////

    bool increment_nonce(Address const &address)
    {
        auto &account = current_account(address);
        auto const nonce = account.has_value() ? account->nonce : 0;
        if (nonce == std::numeric_limits<decltype(nonce)>::max()) {
            // Match geth behavior - don't overflow nonce
            return false;
        }
        if (MONAD_UNLIKELY(!account.has_value())) {
            account = Account{.incarnation = incarnation_};
        }
        account->nonce = nonce + 1;
        return true;
    }

    void set_nonce(Address const &address, uint64_t const nonce)
    {
        auto &account = current_account(address);
        if (MONAD_UNLIKELY(!account.has_value())) {
            account = Account{.incarnation = incarnation_};
        }
        account.value().nonce = nonce;
    }

    void add_to_balance(Address const &address, uint256_t const &delta)
    {
        auto &account_state = current_account_state(address);
        auto &account = account_state.account_;
        if (MONAD_UNLIKELY(!account.has_value())) {
            account = Account{.incarnation = incarnation_};
        }

        MONAD_ASSERT(
            std::numeric_limits<uint256_t>::max() - delta >=
            account.value().balance);

        account.value().balance += delta;
        account_state.touch();
    }

    void subtract_from_balance(Address const &address, uint256_t const &delta)
    {
        auto &account_state = current_account_state(address);
        auto &account = account_state.account_;
        if (MONAD_UNLIKELY(!account.has_value())) {
            account = Account{.incarnation = incarnation_};
        }

        MONAD_ASSERT(delta <= account.value().balance);

        account.value().balance -= delta;
        account_state.touch();
    }

    void set_code_hash(Address const &address, bytes32_t const &hash)
    {
        auto &account = current_account(address);
        MONAD_ASSERT(account.has_value());
        account.value().code_hash = hash;
    }

    evmc_storage_status set_storage(
        Address const &address, bytes32_t const &key, bytes32_t const &value)
    {
        bytes32_t original_value;
        auto &account_state = current_account_state(address);
        MONAD_ASSERT(account_state.account_);
        // original
        {
            auto &orig_account_state = original_account_state(address);
            auto &storage = orig_account_state.storage_;
            auto it = storage.find(key);
            if (it == storage.end()) {
                Incarnation const incarnation =
                    account_state.account_->incarnation;
#if 1
                auto fn1 = [this] { read_speculation_.pre_read(); };
                auto fn2 = [this](bool hasval) {
                    read_speculation_.post_read(hasval);
                };
                bytes32_t const value = [&] {
                    if (use_read_speculation()) {
                        return block_state_.read_storage(
                            address, incarnation, key, fn1, fn2);
                    }
                    else {
                        return block_state_.read_storage(
                            address, incarnation, key);
                    }
                }();
#else
                bytes32_t const value =
                    block_state_.read_storage(address, incarnation, key);
#endif
                it = storage.try_emplace(key, value).first;
            }
            original_value = it->second;
        }
        // state
        {
            auto const result =
                account_state.set_storage(key, value, original_value);
            return result;
        }
    }

    void set_transient_storage(
        Address const &address, bytes32_t const &key, bytes32_t const &value)
    {
        current_account_state(address).set_transient_storage(key, value);
    }

    void touch(Address const &address)
    {
        auto &account_state = current_account_state(address);
        account_state.touch();
    }

    evmc_access_status access_account(Address const &address)
    {
        auto &account_state = current_account_state(address);
        return account_state.access();
    }

    evmc_access_status
    access_storage(Address const &address, bytes32_t const &key)
    {
        auto &account_state = current_account_state(address);
        return account_state.access_storage(key);
    }

    ////////////////////////////////////////

    template <evmc_revision rev>
    bool selfdestruct(Address const &address, Address const &beneficiary)
    {
        auto &account_state = current_account_state(address);
        auto &account = account_state.account_;
        MONAD_ASSERT(account.has_value());

        if constexpr (rev < EVMC_CANCUN) {
            add_to_balance(beneficiary, account.value().balance);
            account.value().balance = 0;
            original_account_state(address).set_validate_exact_balance();
        }
        else {
            if (address != beneficiary ||
                account->incarnation == incarnation_) {
                add_to_balance(beneficiary, account.value().balance);
                account.value().balance = 0;
                original_account_state(address).set_validate_exact_balance();
            }
        }

        return account_state.destruct();
    }

    // YP (87)
    template <evmc_revision rev>
    void destruct_suicides()
    {
        MONAD_ASSERT(!version_);

        for (auto it = current_.begin(); it != current_.end(); ++it) {
            auto &stack = it->second;
            MONAD_ASSERT(stack.size() == 1);
            MONAD_ASSERT(stack.version() == 0);
            auto &account_state = stack.current(0);
            if (account_state.is_destructed()) {
                auto &account = account_state.account_;
                if constexpr (rev < EVMC_CANCUN) {
                    account.reset();
                }
                else {
                    if (account->incarnation == incarnation_) {
                        account.reset();
                    }
                }
            }
        }
    }

    // YP (88)
    void destruct_touched_dead()
    {
        MONAD_ASSERT(!version_);

        for (auto it = current_.begin(); it != current_.end(); ++it) {
            auto &stack = it->second;
            MONAD_ASSERT(stack.size() == 1);
            MONAD_ASSERT(stack.version() == 0);
            auto &account_state = stack.current(0);
            if (MONAD_LIKELY(!account_state.is_touched())) {
                continue;
            }
            auto &account = account_state.account_;
            if (is_dead(account)) {
                account.reset();
            }
        }
    }

    ////////////////////////////////////////

    /**
     * TODO code return reference
     */

    std::shared_ptr<CodeAnalysis> get_code(Address const &address)
    {
        auto const &account = recent_account(address);
        if (MONAD_UNLIKELY(!account.has_value())) {
            return std::make_shared<CodeAnalysis>(analyze({}));
        }
        bytes32_t const &code_hash = account.value().code_hash;
        {
            auto const it = code_.find(code_hash);
            if (it != code_.end()) {
                return it->second;
            }
        }
        return block_state_.read_code(code_hash);
    }

    size_t get_code_size(Address const &address)
    {
        auto const &account = recent_account(address);
        if (MONAD_UNLIKELY(!account.has_value())) {
            return 0;
        }
        bytes32_t const &code_hash = account.value().code_hash;
        {
            auto const it = code_.find(code_hash);
            if (it != code_.end()) {
                auto const &code_analysis = it->second;
                MONAD_ASSERT(code_analysis);
                return code_analysis->executable_code().size();
            }
        }
        auto const code_analysis = block_state_.read_code(code_hash);
        MONAD_ASSERT(code_analysis);
        return code_analysis->executable_code().size();
    }

    size_t copy_code(
        Address const &address, size_t const offset, uint8_t *const buffer,
        size_t const buffer_size)
    {
        auto const &account = recent_account(address);
        if (MONAD_UNLIKELY(!account.has_value())) {
            return 0;
        }
        bytes32_t const &code_hash = account.value().code_hash;
        std::shared_ptr<CodeAnalysis> code_analysis{};
        {
            auto const it = code_.find(code_hash);
            if (it != code_.end()) {
                code_analysis = it->second;
            }
            else {
                code_analysis = block_state_.read_code(code_hash);
            }
        }
        MONAD_ASSERT(code_analysis);
        auto const &code = code_analysis->executable_code();
        if (offset > code.size()) {
            return 0;
        }
        auto const n = std::min(code.size() - offset, buffer_size);
        std::copy_n(code.data() + offset, n, buffer);
        return n;
    }

    void set_code(Address const &address, byte_string_view const code)
    {
        auto &account = current_account(address);
        if (MONAD_UNLIKELY(!account.has_value())) {
            return;
        }

        auto const code_hash = to_bytes(keccak256(code));
        code_[code_hash] = std::make_shared<CodeAnalysis>(analyze(code));
        account.value().code_hash = code_hash;
    }

    ////////////////////////////////////////

    void create_contract(Address const &address)
    {
        auto &account = current_account(address);
        if (MONAD_UNLIKELY(account.has_value())) {
            // EIP-684
            MONAD_ASSERT(account->nonce == 0);
            MONAD_ASSERT(account->code_hash == NULL_HASH);
            // keep the balance, per chapter 7 of the YP
            account->incarnation = incarnation_;
        }
        else {
            account = Account{.incarnation = incarnation_};
        }
    }

    ////////////////////////////////////////

    std::vector<Receipt::Log> const &logs()
    {
        return logs_.recent();
    }

    void store_log(Receipt::Log const &log)
    {
        auto &logs = logs_.current(version_);
        logs.push_back(log);
    }

    ////////////////////////////////////////

    void set_to_state_incarnation(Address const &address)
    {
        auto &account = current_account(address);
        if (MONAD_UNLIKELY(!account.has_value())) {
            account = Account{.incarnation = incarnation_};
        }
        account.value().incarnation = incarnation_;
    }
};

MONAD_NAMESPACE_END
