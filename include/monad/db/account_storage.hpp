#pragma once

#include <monad/core/address.hpp>
#include <monad/core/assert.h>
#include <monad/core/bytes.hpp>

#include <monad/db/config.hpp>
#include <monad/db/datum.hpp>

#include <unordered_map>
#include <unordered_set>

MONAD_DB_NAMESPACE_BEGIN

template <class TStorage>
struct AccountStorage
{
    using account_storage_t =
        std::unordered_map<bytes32_t, diff_value<bytes32_t>>;

    AccountStorage(TStorage &store)
        : storage_{store}
    {
    }

    struct InnerStorage
    {
        std::unordered_map<address_t, account_storage_t> storage_{};
        std::unordered_map<
            address_t,
            std::unordered_set<
                deleted_key, deleted_key::hash, deleted_key::equality>>
            deleted_storage_{};

        inline bool
        contains_key(address_t const &a, bytes32_t const &key) const noexcept
        {
            return storage_.contains(a) && storage_.at(a).contains(key);
        }

        inline bool deleted_storage_contains_key(
            address_t const &a, bytes32_t const &key) const noexcept
        {
            return deleted_storage_.contains(a) &&
                   deleted_storage_.at(a).contains(deleted_key{key});
        }

        inline void clear()
        {
            storage_.clear();
            deleted_storage_.clear();
        }
    };

    TStorage &storage_;
    InnerStorage touched_{};
    InnerStorage merged_{};
    std::unordered_map<address_t, std::unordered_set<bytes32_t>>
        accessed_storage_{};

    inline void remove_key(address_t const &a, bytes32_t const &key)
    {
        storage_.at(a).erase(key);
        if (storage_.at(a).empty()) {
            storage_.erase(a);
        }
    }

    inline bool
    remove_merged_key_if_present(address_t const &a, bytes32_t const &key)
    {
        if (merged_.contains_key(a, key)) {
            merged_.storage_.at(a).erase(key);
            if (merged_.storage_.at(a).empty()) {
                merged_.storage_.erase(a);
            }
            return true;
        }
        return false;
    }

    inline void remove_touched_key(address_t const &a, bytes32_t const &key)
    {
        touched_.storage_.at(a).erase(key);
        if (touched_.storage_.at(a).empty()) {
            touched_.storage_.erase(a);
        }
    }

    inline bool storage_contains_key(
        address_t const &a, bytes32_t const &key) const noexcept
    {
        return storage_.contains(a) && storage_.at(a).contains(key);
    }

    inline bool storage_or_merged_contains_key(
        address_t const &a, bytes32_t const &key) const noexcept
    {
        return (!merged_.deleted_storage_contains_key(a, key)) &&
               (merged_.contains_key(a, key) || storage_contains_key(a, key));
    }

    [[nodiscard]] inline bytes32_t get_committed_storage(
        address_t const &a, bytes32_t const &key) const noexcept
    {
        if (merged_.deleted_storage_contains_key(a, key)) {
            return {};
        }
        if (merged_.contains_key(a, key)) {
            return merged_.storage_.at(a).at(key).value;
        }
        if (storage_contains_key(a, key)) {
            return storage_.at(a).at(key);
        }
        return {};
    }

    [[nodiscard]] inline bytes32_t
    get_storage(address_t const &a, bytes32_t const &key) const noexcept
    {
        if (touched_.deleted_storage_contains_key(a, key)) {
            return {};
        }
        if (touched_.contains_key(a, key)) {
            return touched_.storage_.at(a).at(key).value;
        }
        if (merged_.deleted_storage_contains_key(a, key)) {
            return {};
        }
        if (merged_.contains_key(a, key)) {
            return merged_.storage_.at(a).at(key).value;
        }
        if (storage_contains_key(a, key)) {
            return storage_.at(a).at(key);
        }
        return {};
    }

    [[nodiscard]] inline evmc_storage_status
    zero_out_key(address_t const &a, bytes32_t const &key) noexcept
    {
        // Assume empty (zero) storage is not stored in storage_
        if (storage_or_merged_contains_key(a, key)) {
            if (touched_.contains_key(a, key)) {
                if (get_committed_storage(a, key) ==
                    touched_.storage_.at(a).at(key)) {
                    remove_touched_key(a, key);
                    return EVMC_STORAGE_DELETED;
                }
                else {
                    remove_touched_key(a, key);
                    touched_.deleted_storage_[a].insert(
                        deleted_key{storage_.at(a).at(key), key});
                    return EVMC_STORAGE_MODIFIED_DELETED;
                }
            }
            else {
                touched_.deleted_storage_[a].insert(
                    deleted_key{get_committed_storage(a, key), key});
                return EVMC_STORAGE_DELETED;
            }
        }

        if (touched_.contains_key(a, key)) {
            remove_touched_key(a, key);
            return EVMC_STORAGE_ADDED_DELETED;
        }
        return EVMC_STORAGE_ASSIGNED;
    }

    [[nodiscard]] inline evmc_storage_status set_current_value(
        address_t const &a, bytes32_t const &key,
        bytes32_t const &value) noexcept
    {
        if (storage_or_merged_contains_key(a, key)) {
            if (touched_.contains_key(a, key)) {
                if (touched_.storage_[a][key].value == value) {
                    return EVMC_STORAGE_ASSIGNED;
                }

                if (get_committed_storage(a, key) == value) {
                    remove_touched_key(a, key);
                    return EVMC_STORAGE_MODIFIED_RESTORED;
                }

                touched_.storage_[a][key].value = value;
                return EVMC_STORAGE_MODIFIED;
            }

            touched_.storage_[a].insert(
                {key,
                 diff_value<bytes32_t>{get_committed_storage(a, key), value}});

            if (touched_.deleted_storage_contains_key(a, key)) {
                touched_.deleted_storage_.at(a).erase(deleted_key{key});

                if (get_committed_storage(a, key) == value) {
                    return EVMC_STORAGE_DELETED_RESTORED;
                }
                return EVMC_STORAGE_DELETED_ADDED;
            }

            if (get_committed_storage(a, key) == value) {
                return EVMC_STORAGE_ASSIGNED;
            }
            return EVMC_STORAGE_MODIFIED;
        }

        if (!touched_.storage_.contains(a) ||
            !touched_.storage_.at(a).contains(key)) {
            touched_.storage_[a].insert({key, diff_value<bytes32_t>{value}});
            return EVMC_STORAGE_ADDED;
        }

        touched_.storage_[a][key] = value;
        return EVMC_STORAGE_ASSIGNED;
    }

    [[nodiscard]] evmc_storage_status set_storage(
        address_t const &a, bytes32_t const &key,
        bytes32_t const &value) noexcept
    {
        if (value == bytes32_t{}) {
            return zero_out_key(a, key);
        }
        return set_current_value(a, key, value);
    }

    evmc_access_status
    access_storage(address_t const &a, bytes32_t const &key) noexcept
    {
        auto const &[_, inserted] = accessed_storage_[a].insert(key);
        if (inserted) {
            return EVMC_ACCESS_COLD;
        }
        return EVMC_ACCESS_WARM;
    }

    inline bool can_commit() const
    {
        for (auto const &[a, key_set] : merged_.deleted_storage_) {
            for (auto const &[orig, key] : key_set) {
                if (storage_contains_key(a, key)) {
                    if (storage_.at(a).at(key) != orig) {
                        return false;
                    }
                }
                else if (orig != bytes32_t{}) {
                    return false;
                }
            }
        }
        for (auto const &[a, keys] : merged_.storage_) {
            for (auto const &[k, dv] : keys) {
                if (dv.orig == bytes32_t{}) {
                    continue;
                }

                if (storage_.at(a).at(k) != dv.orig) {
                    return false;
                }
            }
        }
        return true;
    }

    inline void commit_all_merged()
    {
        MONAD_ASSERT(can_commit());

        for (auto const &[addr, key_set] : merged_.deleted_storage_) {
            for (auto const &key : key_set) {
                remove_key(addr, key.key);
            }
        }
        for (auto const &[addr, acct_storage] : merged_.storage_) {
            for (auto const &[key, value] : acct_storage) {
                MONAD_ASSERT(value.value != bytes32_t{});
                storage_[addr].insert_or_assign(key, value.value);
            }
        }
    }

    inline void revert_touched()
    {
        touched_.clear();
        accessed_storage_.clear();
    }

    inline AccountStorage get_copy() const
    {
        AccountStorage a(*this);
        return a;
    }

    inline bool can_merge(AccountStorage const &diffs)
    {
        for (auto const &[a, key_set] : diffs.touched_.deleted_storage_) {
            for (auto const &k : key_set) {
                if (k.orig_value != get_committed_storage(a, k.key)) {
                    return false;
                }

                if (merged_.deleted_storage_contains_key(a, k.key)) {
                    return false;
                }
            }
        }

        for (auto const &[a, keys] : diffs.touched_.storage_) {
            for (auto const &[k, v] : keys) {
                if (v.orig != get_committed_storage(a, k)) {
                    return false;
                }
            }
        }
        return true;
    }

    inline void merge_touched(AccountStorage &diffs)
    {
        for (auto &[a, key_set] : diffs.touched_.deleted_storage_) {
            for (auto const &key : key_set) {
                if (auto const removed =
                        remove_merged_key_if_present(a, key.key);
                    removed) {
                    if (storage_contains_key(a, key.key)) {
                        merged_.deleted_storage_[a].insert(
                            {key, {storage_.at(a).at(key.key), key.key}});
                    }
                }
                else if (storage_contains_key(a, key.key)) {
                    merged_.deleted_storage_[a].insert(key);
                }
            }
        }

        for (auto &[addr, acct_storage] : diffs.touched_.storage_) {
            if (!merged_.storage_.contains(addr)) {
                merged_.storage_.emplace(
                    std::make_pair(addr, std::move(acct_storage)));
                continue;
            }

            for (auto const &[key, value] : acct_storage) {
                MONAD_ASSERT(value != bytes32_t{});
                merged_.storage_.at(addr).at(key).value = value.value;
            }
        }
    }
};

MONAD_DB_NAMESPACE_END
