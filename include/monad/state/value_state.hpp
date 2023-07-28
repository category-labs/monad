#pragma once

#include "monad/state/state.hpp"
#include <monad/core/address.hpp>
#include <monad/core/assert.h>
#include <monad/core/bytes.hpp>

#include <monad/state/config.hpp>
#include <monad/state/datum.hpp>
#include <monad/state/state_changes.hpp>

#include <unordered_map>
#include <unordered_set>

MONAD_STATE_NAMESPACE_BEGIN

template <class TValueDB>
struct ValueState
{
    using diff_t = diff<bytes32_t>;
    using key_value_map_t = std::unordered_map<bytes32_t, diff_t>;

    struct InnerStorage
    {
        std::unordered_map<address_t, key_value_map_t> storage_{};
        std::unordered_map<
            address_t,
            std::unordered_set<
                deleted_key, deleted_key::hash, deleted_key::equality>>
            deleted_storage_{};

        bool
        contains_key(address_t const &a, bytes32_t const &key) const noexcept
        {
            return storage_.contains(a) && storage_.at(a).contains(key);
        }

        bool deleted_contains_key(
            address_t const &a, bytes32_t const &key) const noexcept
        {
            return deleted_storage_.contains(a) &&
                   deleted_storage_.at(a).contains(deleted_key{key});
        }

        void clear()
        {
            storage_.clear();
            deleted_storage_.clear();
        }
    };

    struct WorkingCopy;

    ValueState(TValueDB &store)
        : db_{store}
    {
    }

    TValueDB &db_;
    InnerStorage merged_{};

    bool remove_merged_key_if_present(address_t const &a, bytes32_t const &key)
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

    bool db_or_merged_contains_key(
        address_t const &a, bytes32_t const &key) const noexcept
    {
        return (!merged_.deleted_contains_key(a, key)) &&
               (merged_.contains_key(a, key) || db_.contains(a, key));
    }

    [[nodiscard]] bytes32_t
    get_merged_value(address_t const &a, bytes32_t const &key) const noexcept
    {
        if (merged_.deleted_contains_key(a, key)) {
            return {};
        }
        if (merged_.contains_key(a, key)) {
            return merged_.storage_.at(a).at(key).updated;
        }
        return db_.try_find(a, key).value_or(bytes32_t{});
    }

    // Note: just for debug testing
    bool can_commit() const noexcept
    {
        for (auto const &[a, key_set] : merged_.deleted_storage_) {
            for (auto const &[orig, key] : key_set) {
                if (db_.try_find(a, key).value_or(bytes32_t{}) != orig) {
                    return false;
                }
            }
        }
        for (auto const &[a, keys] : merged_.storage_) {
            for (auto const &[k, dv] : keys) {
                if (dv.orig == bytes32_t{}) {
                    continue;
                }

                if (db_.at(a, k) != dv.orig) {
                    return false;
                }
            }
        }
        return true;
    }

    StateChanges::StorageChanges gather_changes() const
    {
        assert(can_commit());
        StateChanges::StorageChanges storage_changes;

        for (auto const &[addr, key_set] : merged_.deleted_storage_) {
            for (auto const &key : key_set) {
                storage_changes[addr].emplace_back(key.key, bytes32_t{});
            }
        }
        for (auto const &[addr, acct_storage] : merged_.storage_) {
            for (auto const &[key, value] : acct_storage) {
                assert(value.updated != bytes32_t{});
                storage_changes[addr].emplace_back(key, value.updated);
            }
        }
        return storage_changes;
    }

    void clear_changes() { merged_.clear(); }

    bool can_merge(WorkingCopy const &diffs) const noexcept
    {
        for (auto const &[a, key_set] : diffs.touched_.deleted_storage_) {
            for (auto const &k : key_set) {
                if (k.orig_value != get_merged_value(a, k.key)) {
                    return false;
                }
            }
        }

        for (auto const &[a, keys] : diffs.touched_.storage_) {
            for (auto const &[k, v] : keys) {
                if (v.orig != get_merged_value(a, k)) {
                    return false;
                }
            }
        }
        return true;
    }

    void merge_touched(WorkingCopy &diffs)
    {
        MONAD_DEBUG_ASSERT(can_merge(diffs));

        for (auto &[a, key_set] : diffs.touched_.deleted_storage_) {
            for (auto const &key : key_set) {
                if (remove_merged_key_if_present(a, key.key)) {
                    if (db_.contains(a, key.key)) {
                        merged_.deleted_storage_[a].insert(
                            {key, {db_.at(a, key.key), key.key}});
                    }
                }
                else if (db_.contains(a, key.key)) {
                    merged_.deleted_storage_[a].insert(key);
                }
            }
        }

        for (auto &[addr, acct_storage] : diffs.touched_.storage_) {
            if (!merged_.storage_.contains(addr)) {
                merged_.storage_.emplace(addr, std::move(acct_storage));
                continue;
            }

            for (auto const &[key, value] : acct_storage) {
                assert(value != bytes32_t{});
                merged_.storage_.at(addr).at(key).updated = value.updated;
            }
        }
    }
};

template <typename TValueDB>
struct ValueState<TValueDB>::WorkingCopy : public ValueState<TValueDB>
{
    InnerStorage touched_{};
    std::unordered_map<address_t, std::unordered_set<bytes32_t>>
        accessed_storage_{};
    void remove_touched_key(address_t const &a, bytes32_t const &key)
    {
        touched_.storage_.at(a).erase(key);
        if (touched_.storage_.at(a).empty()) {
            touched_.storage_.erase(a);
        }
    }

    // EVMC Host Interface
    [[nodiscard]] bytes32_t
    get_storage(address_t const &a, bytes32_t const &key) const noexcept
    {
        if (touched_.deleted_contains_key(a, key)) {
            return {};
        }
        if (touched_.contains_key(a, key)) {
            return touched_.storage_.at(a).at(key).updated;
        }
        return get_merged_value(a, key);
    }

    [[nodiscard]] evmc_storage_status
    zero_out_key(address_t const &a, bytes32_t const &key) noexcept
    {
        auto const merged_value = get_merged_value(a, key);
        // Assume empty (zero) storage is not stored in storage_
        if (merged_value != bytes32_t{}) {
            if (touched_.contains_key(a, key)) {
                if (merged_value == touched_.storage_.at(a).at(key)) {
                    remove_touched_key(a, key);
                    return EVMC_STORAGE_DELETED;
                }
                else {
                    remove_touched_key(a, key);
                    touched_.deleted_storage_[a].insert(
                        deleted_key{db_.at(a, key), key});
                    return EVMC_STORAGE_MODIFIED_DELETED;
                }
            }
            else {
                touched_.deleted_storage_[a].insert(
                    deleted_key{merged_value, key});
                return EVMC_STORAGE_DELETED;
            }
        }

        if (touched_.contains_key(a, key)) {
            remove_touched_key(a, key);
            return EVMC_STORAGE_ADDED_DELETED;
        }
        return EVMC_STORAGE_ASSIGNED;
    }

    [[nodiscard]] evmc_storage_status set_current_value(
        address_t const &a, bytes32_t const &key,
        bytes32_t const &value) noexcept
    {
        auto const merged_value = get_merged_value(a, key);
        if (merged_value != bytes32_t{}) {
            if (touched_.contains_key(a, key)) {
                if (touched_.storage_[a][key].updated == value) {
                    return EVMC_STORAGE_ASSIGNED;
                }

                if (merged_value == value) {
                    remove_touched_key(a, key);
                    return EVMC_STORAGE_MODIFIED_RESTORED;
                }

                if (touched_.storage_[a][key].updated == merged_value) {
                    touched_.storage_[a][key].updated = value;
                    return EVMC_STORAGE_MODIFIED;
                }

                touched_.storage_[a][key].updated = value;
                return EVMC_STORAGE_ASSIGNED;
            }

            touched_.storage_[a].emplace(key, diff_t{merged_value, value});

            if (touched_.deleted_contains_key(a, key)) {
                touched_.deleted_storage_.at(a).erase(deleted_key{key});

                if (merged_value == value) {
                    return EVMC_STORAGE_DELETED_RESTORED;
                }
                return EVMC_STORAGE_DELETED_ADDED;
            }

            if (merged_value == value) {
                return EVMC_STORAGE_ASSIGNED;
            }
            return EVMC_STORAGE_MODIFIED;
        }

        if (!touched_.storage_.contains(a) ||
            !touched_.storage_.at(a).contains(key)) {
            touched_.storage_[a].emplace(key, diff_t{value});
            return EVMC_STORAGE_ADDED;
        }

        touched_.storage_[a][key] = value;
        return EVMC_STORAGE_ASSIGNED;
    }

    // EVMC Host Interface
    [[nodiscard]] evmc_storage_status set_storage(
        address_t const &a, bytes32_t const &key,
        bytes32_t const &value) noexcept
    {
        if (value == bytes32_t{}) {
            return zero_out_key(a, key);
        }
        return set_current_value(a, key, value);
    }

    // EVMC Host Interface
    evmc_access_status
    access_storage(address_t const &a, bytes32_t const &key) noexcept
    {
        auto const &[_, inserted] = accessed_storage_[a].insert(key);
        if (inserted) {
            return EVMC_ACCESS_COLD;
        }
        return EVMC_ACCESS_WARM;
    }

    void revert() noexcept
    {
        touched_.clear();
        accessed_storage_.clear();
    }
};

MONAD_STATE_NAMESPACE_END
