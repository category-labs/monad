// Copyright (C) 2025-26 Category Labs, Inc.
//
// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with this program.  If not, see <http://www.gnu.org/licenses/>.

#include <zkvm/state/state.hpp>

#include <category/core/address.hpp>
#include <category/core/assert.h>
#include <category/core/byte_string.hpp>
#include <category/core/bytes.hpp>
#include <category/core/cases.hpp>
#include <category/core/config.hpp>
#include <category/core/int.hpp>
#include <category/core/keccak.hpp>
#include <category/core/likely.h>
#include <category/core/monad_exception.hpp>
#include <category/execution/ethereum/core/account.hpp>
#include <category/execution/ethereum/core/receipt.hpp>
#include <category/execution/ethereum/db/offset_trie.hpp>
#include <category/execution/ethereum/state3/state_interface.hpp>
#include <category/execution/ethereum/types/incarnation.hpp>
#include <category/vm/code.hpp>
#include <category/vm/evm/access_status.hpp>
#include <category/vm/evm/page_storage_status.hpp>
#include <category/vm/evm/storage_status.hpp>
#include <category/vm/vm.hpp>
#include <zkvm/state/account_state.hpp>
#include <zkvm/state/key_hash.hpp>
#include <zkvm/state/slot_map.hpp>

#include <cstdint>
#include <cstring>
#include <limits>
#include <optional>
#include <span>
#include <utility>
#include <vector>

MONAD_NAMESPACE_BEGIN

namespace zkvm
{
    namespace
    {
        // Initial capacities; see SLOT_RESERVE for why containers get floors.
        constexpr size_t ACCOUNTS_RESERVE = 1024;
        constexpr size_t EPOCH_ACCOUNT_STATES_RESERVE = 256;

        bytes32_t const ZERO{};
    }

    State::State(
        mpt::OffsetTrie trie, CodeTable codes, vm::VM &vm,
        uint64_t const block_number, KeySeed const &seed)
        : seed_{seed}
        , trie_{std::move(trie)}
        , codes_{std::move(codes)}
        , vm_{vm}
        , accounts_{seed_, ACCOUNTS_RESERVE}
        , block_number_{block_number}
    {
        // A witness account carries Incarnation{0, 0}; no stamp may equal it.
        MONAD_ASSERT(block_number != 0);
        // A real seed, and one seed for every table: the code table's
        // buckets must be the ones its lookups hash to.
        MONAD_ASSERT(seed_.seeded(), "zkvm State: unseeded key hash");
        MONAD_ASSERT(
            codes_.hash_function().seed == seed_,
            "zkvm State: code table seed differs");
        // The empty code, so that read_code(NULL_HASH) never misses.
        empty_code_ =
            &codes_
                 .try_emplace(
                     NULL_HASH, vm_.try_insert_varcode_raw(NULL_HASH, {}))
                 .first->second;
        // Floors: the arena never frees, so growth is a copy and a leak.
        epoch_account_states_.reserve(EPOCH_ACCOUNT_STATES_RESERVE);
    }

    ////////////////////////////////////////
    // Rows and witness reads

    ////////////////////////////////////////
    // Rows

    AccountState &State::account_state_for(Address const &address)
    {
        auto const [account_state, inserted] =
            accounts_.find_or_emplace(address);
        if (inserted) {
            resolve_account(address, account_state);
        }
        if (inserted || account_state.epoch != epoch_) {
            begin_epoch(account_state);
        }
        return account_state;
    }

    void
    State::resolve_account(Address const &address, AccountState &account_state)
    {
        account_state.addr_hash = to_bytes(keccak256(address.bytes));
        auto const found = trie_.try_find_original(
            trie_.root, key_path(account_state.addr_hash));
        if (!found.has_value()) {
            account_state.resolution = AccountResolution::Unproven;
            return;
        }
        mpt::match(
            *found,
            Cases{
                [&](mpt::NullView) {
                    account_state.resolution = AccountResolution::Absent;
                },
                [&](mpt::AccountLeafView const l) {
                    account_state.resolution = AccountResolution::Present;
                    account_state.leaf = trie_.id_of(l);
                    account_state.storage_root = l.storage();
                    account_state.account_ = l.account();
                },
                [](auto) {
                    MONAD_ABORT("zkvm State: account walk ended off a leaf");
                }});
    }

    SlotState &State::slot(AccountState &account_state, bytes32_t const &key)
    {
        SlotState *const found = account_state.storage.find(key);
        if (found != nullptr) {
            if (found->epoch != epoch_) {
                found->epoch = epoch_;
                found->accessed = false;
                if (found->written) {
                    // What the slot reads as becomes its transaction-start
                    // value: `current`, or zero if a preceding transaction
                    // deleted the account and it has since been re-created.
                    // A written slot never walks the trie here.
                    found->tx_start =
                        account_state.current_value(*found, trie_);
                }
            }
            return *found;
        }
        SlotState &s = account_state.storage.emplace(key);
        s.epoch = epoch_;
        return s;
    }

    void State::begin_epoch(AccountState &account_state)
    {
        account_state.epoch = epoch_;
        account_state.accessed = false;
        account_state.touched = false;
        account_state.destructed = false;
        account_state.transient_storage.clear();
        epoch_account_states_.push_back(&account_state);
    }

    std::optional<Account> const &State::recent_account(Address const &address)
    {
        return account_state_for(address).account();
    }

    Account &State::ensure_account(AccountState &account_state)
    {
        auto &acct = account_state.account();
        if (MONAD_UNLIKELY(!acct.has_value())) {
            journal_.created(account_state);
            acct = Account{.incarnation = incarnation()};
        }
        account_state.written = true;
        return *acct;
    }

    ////////////////////////////////////////
    // Block lifecycle

    void State::begin_transaction(uint64_t const i)
    {
        MONAD_ASSERT(!journal_.open(), "zkvm State: frame open at tx start");
        MONAD_ASSERT(epoch_ == i, "zkvm State: transactions out of order");
        MONAD_ASSERT(journal_.logs().empty(), "zkvm State: logs not taken");
        epoch_account_states_.clear();
        epoch_ = i + 1;
    }

    std::vector<Receipt::Log> State::take_logs()
    {
        return journal_.take_logs();
    }

    bool
    State::commit_storage(AccountState &account_state, mpt::NodeId &storage)
    {
        Account const &acct = *account_state.account_;
        bool const recreated = acct.incarnation != WITNESS_INCARNATION;
        bool changed = false;

        // What the slot holds in the pre-state: nothing under a re-created
        // account, whose storage starts over; otherwise the witness value,
        // walked now if no read resolved it.
        auto const pre_value = [&](SlotState &s) -> bytes32_t const & {
            if (recreated) {
                return ZERO;
            }
            if (!s.resolved &&
                MONAD_UNLIKELY(!account_state.resolve_slot(s, trie_))) {
                MONAD_ABORT("zkvm State: storage slot not in the witness");
            }
            return s.block_start;
        };
        auto const post_value = [&](SlotState const &s) -> bytes32_t const & {
            return account_state.stamp_is_live(s) ? s.current : ZERO;
        };

        // Upserts before erases: an erase can collapse a branch, and the
        // collapse must not meet a digest an upsert would have replaced.
        for (SlotState &s : account_state.storage) {
            if (!s.written) {
                continue;
            }
            bytes32_t const &post = post_value(s);
            if (post == ZERO || post == pre_value(s)) {
                continue;
            }
            if (!s.resolved) {
                // Never read, so never hashed.
                s.key_hash = to_bytes(keccak256(s.key.bytes));
            }
            auto const [leaf, path] =
                trie_.upsert_node(storage, key_path(s.key_hash));
            if (storage == mpt::NULL_ID) {
                storage = leaf;
            }
            trie_.put_storage(leaf, mpt::NibblesView{path}, post);
            changed = true;
        }
        if (recreated) {
            return changed;
        }
        for (SlotState &s : account_state.storage) {
            if (!s.written || post_value(s) != ZERO || pre_value(s) == ZERO) {
                continue;
            }
            if (trie_.erase_node(storage, key_path(s.key_hash)) ==
                mpt::OffsetTrie::EraseResult::Erased) {
                storage = mpt::NULL_ID;
            }
            changed = true;
        }
        return changed;
    }

    void State::commit()
    {
        MONAD_ASSERT(!journal_.open(), "zkvm State: commit inside a frame");

        // Pass 1: the accounts the post-state holds. Only a written row can
        // differ from the witness; one whose writes all rolled back or
        // restored the pre-state decodes equal and is skipped.
        for (auto &[address, account_state] : accounts_) {
            if (!account_state.written || !account_state.account_.has_value()) {
                continue;
            }
            MONAD_ASSERT(
                account_state.resolution != AccountResolution::Unproven);
            Account const &acct = *account_state.account_;
            bool const present =
                account_state.resolution == AccountResolution::Present;
            bool const recreated = acct.incarnation != WITNESS_INCARNATION;
            bool account_changed = !present || recreated;
            if (!account_changed) {
                // The witness leaf, read from the blob: the upsert below may
                // rewrite its path, so this goes through get_original.
                account_changed =
                    mpt::AccountLeafView{trie_.get_original(account_state.leaf)}
                        .account() != acct;
            }
            mpt::NodeId storage =
                recreated ? mpt::NULL_ID : account_state.storage_root;
            bool const storage_changed = commit_storage(account_state, storage);
            if (!account_changed && !storage_changed) {
                continue;
            }
            auto const [leaf, path] = trie_.upsert_node(
                trie_.root, key_path(account_state.addr_hash));
            if (trie_.root == mpt::NULL_ID) {
                // The first account into an empty trie is the root.
                trie_.root = leaf;
            }
            trie_.put_acct(leaf, mpt::NibblesView{path}, acct, storage);
        }

        // Pass 2: the accounts the block deleted, after every upsert for the
        // same reason the storage erases come last.
        for (auto &[address, account_state] : accounts_) {
            if (!account_state.written || account_state.account_.has_value() ||
                account_state.resolution != AccountResolution::Present) {
                continue;
            }
            if (trie_.erase_node(
                    trie_.root, key_path(account_state.addr_hash)) ==
                mpt::OffsetTrie::EraseResult::Erased) {
                trie_.root = mpt::NULL_ID;
            }
        }
    }

    bytes32_t State::state_root()
    {
        // The pre-state root before commit, the post-state root after.
        return trie_.state_root();
    }

    ////////////////////////////////////////
    // Call frames

    void State::push()
    {
        journal_.push();
    }

    void State::pop_accept()
    {
        journal_.pop_accept();
    }

    void State::pop_reject()
    {
        journal_.pop_reject();
    }

    vm::VM &State::vm()
    {
        return vm_;
    }

    ////////////////////////////////////////
    // Account reads

    uint256_t State::get_balance(Address const &address)
    {
        auto const &account = recent_account(address);
        if (MONAD_LIKELY(account.has_value())) {
            return account->balance;
        }
        return 0;
    }

    bool State::is_destructed(Address const &address)
    {
        return account_state_for(address).destructed;
    }

    bool State::is_current_incarnation(Address const &address)
    {
        auto const &account = recent_account(address);
        if (MONAD_LIKELY(account.has_value())) {
            return account->incarnation == incarnation();
        }
        return false;
    }

    bool State::is_touched(Address const &address)
    {
        return account_state_for(address).touched;
    }

    ////////////////////////////////////////
    // Account writes

    void State::set_nonce(Address const &address, uint64_t const nonce)
    {
        AccountState &account_state = account_state_for(address);
        bool const existed = account_state.account().has_value();
        Account &acct = ensure_account(account_state);
        if (existed) {
            journal_.nonce(account_state, acct.nonce);
        }
        acct.nonce = nonce;
    }

    void State::add_to_balance(Address const &address, uint256_t const &delta)
    {
        AccountState &account_state = account_state_for(address);
        Account &acct = ensure_account(account_state);
        // A zero delta still touches the account but has nothing to undo.
        if (delta != 0) {
            MONAD_ASSERT_THROW(
                std::numeric_limits<uint256_t>::max() - delta >= acct.balance,
                "balance overflow");
            journal_.balance(account_state, acct.balance);
            acct.balance += delta;
        }
        touch(address);
    }

    void
    State::subtract_from_balance(Address const &address, uint256_t const &delta)
    {
        AccountState &account_state = account_state_for(address);
        Account &acct = ensure_account(account_state);
        if (delta != 0) {
            MONAD_ASSERT_THROW(delta <= acct.balance, "balance underflow");
            journal_.balance(account_state, acct.balance);
            acct.balance -= delta;
        }
        touch(address);
    }

    void State::touch(Address const &address)
    {
        AccountState &account_state = account_state_for(address);
        if (!account_state.touched) {
            journal_.touched(account_state);
            account_state.touched = true;
        }
    }

    void State::create_contract(Address const &address)
    {
        AccountState &account_state = account_state_for(address);
        auto &acct = account_state.account();
        if (MONAD_UNLIKELY(acct.has_value())) {
            // EIP-684
            MONAD_ASSERT(acct->nonce == 0);
            MONAD_ASSERT(acct->code_hash == NULL_HASH);
            // Keep the balance, per chapter 7 of the YP. The new stamp hides
            // every slot written under the old one and tells commit to start
            // the storage from empty.
            journal_.account(account_state);
            acct->incarnation = incarnation();
            account_state.written = true;
        }
        else {
            ensure_account(account_state);
        }
    }

    void State::create_account_no_rollback(Address const &address)
    {
        AccountState &account_state = account_state_for(address);
        auto &acct = account_state.account();
        MONAD_ASSERT(!acct.has_value());
        journal_.created(account_state);
        acct = Account{
            .incarnation = Incarnation{block_number_, Incarnation::LAST_TX}};
        account_state.written = true;
    }

    void State::set_to_state_incarnation(Address const &address)
    {
        AccountState &account_state = account_state_for(address);
        bool const existed = account_state.account().has_value();
        if (existed) {
            journal_.account(account_state);
        }
        Account &acct = ensure_account(account_state);
        acct.incarnation = incarnation();
    }

    template <SelfdestructRule rule>
    std::pair<bool, uint256_t>
    State::selfdestruct_impl(Address const &address, Address const &beneficiary)
    {
        AccountState &account_state = account_state_for(address);
        uint256_t const balance = get_balance(address);

        if (address != beneficiary) {
            add_to_balance(beneficiary, balance);
            subtract_from_balance(address, balance);
        }
        // A transfer to the account itself burns the balance exactly when
        // the rule would delete the account.
        else if constexpr (rule == SelfdestructRule::DeleteAll) {
            subtract_from_balance(address, balance);
        }
        else if constexpr (
            rule == SelfdestructRule::DeleteCreatedInTransaction) {
            if (is_current_incarnation(address)) {
                subtract_from_balance(address, balance);
            }
        }

        bool const inserted = !account_state.destructed;
        if (inserted) {
            journal_.destructed(account_state);
            account_state.destructed = true;
        }
        return {inserted, balance};
    }

    template std::pair<bool, uint256_t>
    State::selfdestruct_impl<SelfdestructRule::DeleteAll>(
        Address const &, Address const &);
    template std::pair<bool, uint256_t>
    State::selfdestruct_impl<SelfdestructRule::DeleteCreatedInTransaction>(
        Address const &, Address const &);
    template std::pair<bool, uint256_t>
    State::selfdestruct_impl<SelfdestructRule::ClearCreatedInTransaction>(
        Address const &, Address const &);

    // YP (87). The two end-of-transaction walks run outside any frame.
    template <SelfdestructRule rule>
    void State::destruct_suicides_impl()
    {
        MONAD_ASSERT(!journal_.open(), "zkvm State: destruct inside a frame");

        for (AccountState *const account_state : epoch_account_states_) {
            if (MONAD_LIKELY(!account_state->destructed)) {
                continue;
            }
            auto &acct = account_state->account();
            MONAD_ASSERT(acct.has_value());
            account_state->written = true;

            if constexpr (rule == SelfdestructRule::DeleteAll) {
                acct.reset();
                continue;
            }

            // EIP-6780: only an account created in this transaction is
            // destroyed.
            if (acct->incarnation != incarnation()) {
                continue;
            }

            if constexpr (
                rule == SelfdestructRule::DeleteCreatedInTransaction) {
                acct.reset();
                continue;
            }

            // EIP-8246: nonce reset, code and storage cleared, balance
            // unchanged.
            acct->nonce = 0;
            acct->code_hash = NULL_HASH;
            if (is_empty(*acct)) { // EIP-161
                acct.reset();
                continue;
            }
            // The account keeps its stamp, which already hides the pre-state
            // storage; the slots written under it are zeroed by hand.
            for (SlotState &s : account_state->storage) {
                if (s.written && s.incarnation == acct->incarnation) {
                    s.current = ZERO;
                }
            }
        }
    }

    template void State::destruct_suicides_impl<SelfdestructRule::DeleteAll>();
    template void State::destruct_suicides_impl<
        SelfdestructRule::DeleteCreatedInTransaction>();
    template void State::destruct_suicides_impl<
        SelfdestructRule::ClearCreatedInTransaction>();

    // YP (88)
    void State::destruct_touched_dead()
    {
        MONAD_ASSERT(!journal_.open(), "zkvm State: destruct inside a frame");

        for (AccountState *const account_state : epoch_account_states_) {
            if (MONAD_LIKELY(!account_state->touched)) {
                continue;
            }
            auto &acct = account_state->account();
            if (is_dead(acct)) {
                acct.reset();
                account_state->written = true;
            }
        }
    }

    ////////////////////////////////////////
    // Storage and warmth

    bytes32_t State::get_storage(Address const &address, bytes32_t const &key)
    {
        AccountState &account_state = account_state_for(address);
        auto const &acct = account_state.account();
        if (MONAD_UNLIKELY(!acct.has_value())) {
            return {};
        }
        return account_state.current_value(slot(account_state, key), trie_);
    }

    std::optional<bytes32_t>
    State::try_get_storage(Address const &address, bytes32_t const &key)
    {
        AccountState &account_state = account_state_for(address);
        auto const &acct = account_state.account();
        if (MONAD_UNLIKELY(!acct.has_value())) {
            return bytes32_t{};
        }
        bytes32_t const *const value =
            account_state.try_current_value(slot(account_state, key), trie_);
        if (value == nullptr) {
            return std::nullopt;
        }
        return *value;
    }

    namespace
    {
        // EIP-2200 classification of a store, from the transaction-start
        // value, the value now and the value being written.
        StorageStatus storage_status(
            bytes32_t const &original, bytes32_t const &current,
            bytes32_t const &value)
        {
            if (value == ZERO) {
                if (current == ZERO) {
                    return StorageStatus::Assigned;
                }
                if (original == current) {
                    return StorageStatus::Deleted;
                }
                if (original == ZERO) {
                    return StorageStatus::AddedDeleted;
                }
                return StorageStatus::ModifiedDeleted;
            }
            if (current == ZERO) {
                if (original == ZERO) {
                    return StorageStatus::Added;
                }
                if (value == original) {
                    return StorageStatus::DeletedRestored;
                }
                return StorageStatus::DeletedAdded;
            }
            if (original == current && original != value) {
                return StorageStatus::Modified;
            }
            if (original == value && original != current) {
                return StorageStatus::ModifiedRestored;
            }
            return StorageStatus::Assigned;
        }
    }

    StorageStatus State::set_storage(
        Address const &address, bytes32_t const &key, bytes32_t const &value)
    {
        AccountState &account_state = account_state_for(address);
        auto const &acct = account_state.account();
        MONAD_ASSERT(acct.has_value());
        SlotState &s = slot(account_state, key);
        // Both may read the witness; copied, since the write below changes
        // what they refer to.
        bytes32_t const current = account_state.current_value(s, trie_);
        bytes32_t const original = account_state.tx_original_value(s, trie_);
        auto const status = storage_status(original, current, value);

        if (!s.written) {
            journal_.slot_created(account_state, s);
        }
        else {
            journal_.slot_value(account_state, s);
        }
        // The first write of the block, or the first under a new incarnation:
        // what the slot read as until now is its transaction-start value.
        if (!s.written || !account_state.stamp_is_live(s)) {
            s.tx_start = current;
            s.incarnation = acct->incarnation;
        }
        s.written = true;
        s.current = value;
        account_state.written = true;
        return status;
    }

    bytes32_t
    State::get_transient_storage(Address const &address, bytes32_t const &key)
    {
        AccountState &account_state = account_state_for(address);
        TransientSlot const *const found =
            account_state.transient_storage.find(key);
        return found != nullptr ? found->value : bytes32_t{};
    }

    void State::set_transient_storage(
        Address const &address, bytes32_t const &key, bytes32_t const &value)
    {
        AccountState &account_state = account_state_for(address);
        TransientSlot *t = account_state.transient_storage.find(key);
        if (t == nullptr) {
            t = &account_state.transient_storage.emplace(key);
        }
        journal_.transient(account_state, *t);
        t->value = value;
    }

    AccessStatus State::access_account(Address const &address)
    {
        AccountState &account_state = account_state_for(address);
        if (account_state.accessed) {
            return AccessStatus::Warm;
        }
        journal_.accessed(account_state);
        account_state.accessed = true;
        return AccessStatus::Cold;
    }

    template <bool page>
    AccessStatus
    State::access_storage_impl(Address const &address, bytes32_t const &key)
    {
        if constexpr (page) {
            MONAD_ABORT("zkvm State: MIP-8 page warmth is not supported");
        }
        else {
            AccountState &account_state = account_state_for(address);
            SlotState &s = slot(account_state, key);
            if (s.accessed) {
                return AccessStatus::Warm;
            }
            journal_.slot_warm(account_state, s);
            s.accessed = true;
            return AccessStatus::Cold;
        }
    }

    template AccessStatus
    State::access_storage_impl<false>(Address const &, bytes32_t const &);
    template AccessStatus
    State::access_storage_impl<true>(Address const &, bytes32_t const &);

    PageStorageStatus
    State::update_page(Address const &, bytes32_t const &, StorageStatus)
    {
        MONAD_ABORT("zkvm State: MIP-8 page accounting is not supported");
    }

    ////////////////////////////////////////
    // Code

    vm::SharedVarcode State::read_code(bytes32_t const &code_hash)
    {
        auto const it = codes_.find(code_hash);
        if (MONAD_UNLIKELY(it == codes_.end())) {
            MONAD_ABORT("zkvm State: code not in the witness");
        }
        return it->second;
    }

    vm::SharedVarcode const &
    State::code_of(AccountState &account_state, Account const &acct)
    {
        if (account_state.code == nullptr ||
            account_state.resolved_code_hash != acct.code_hash) {
            auto const it = codes_.find(acct.code_hash);
            if (MONAD_UNLIKELY(it == codes_.end())) {
                MONAD_ABORT("zkvm State: code not in the witness");
            }
            account_state.code = &it->second;
            account_state.resolved_code_hash = acct.code_hash;
        }
        return *account_state.code;
    }

    vm::SharedVarcode State::get_code(Address const &address)
    {
        AccountState &account_state = account_state_for(address);
        auto const &acct = account_state.account();
        if (MONAD_UNLIKELY(!acct.has_value())) {
            return *empty_code_;
        }
        return code_of(account_state, *acct);
    }

    size_t State::get_code_size(Address const &address)
    {
        AccountState &account_state = account_state_for(address);
        auto const &acct = account_state.account();
        if (MONAD_UNLIKELY(!acct.has_value())) {
            return 0;
        }
        return code_of(account_state, *acct)->intercode()->size();
    }

    size_t State::copy_code(
        Address const &address, size_t const offset, uint8_t *const buffer,
        size_t const buffer_size)
    {
        AccountState &account_state = account_state_for(address);
        auto const &acct = account_state.account();
        if (MONAD_UNLIKELY(!acct.has_value())) {
            return 0;
        }
        return code_of(account_state, *acct)
            ->intercode()
            ->copy_code(offset, buffer, buffer_size);
    }

    void State::set_code(Address const &address, byte_string_view const code)
    {
        AccountState &account_state = account_state_for(address);
        auto &acct = account_state.account();
        if (MONAD_UNLIKELY(!acct.has_value())) {
            return;
        }
        auto const code_hash = to_bytes(keccak256(code));
        if (!codes_.contains(code_hash)) {
            codes_.try_emplace(
                code_hash, vm_.try_insert_varcode_raw(code_hash, code));
        }
        journal_.code_hash(account_state, acct->code_hash);
        acct->code_hash = code_hash;
        account_state.written = true;
    }

    ////////////////////////////////////////
    // Logs

    std::span<Receipt::Log const> State::logs()
    {
        return journal_.logs();
    }

    void State::store_log(Receipt::Log const &log)
    {
        journal_.store_log(log);
    }

    ////////////////////////////////////////

    bool State::record_balance_constraint_for_debit(
        Address const &address, uint256_t const &debit)
    {
        return get_balance(address) >= debit;
    }
}

MONAD_NAMESPACE_END
