#pragma once

#include <monad/config.hpp>
#include <monad/core/address.hpp>
#include <monad/core/bytes.hpp>
#include <monad/core/unordered_map.hpp>

#include <vector>

MONAD_NAMESPACE_BEGIN

/**
 * Implements the transient (transaction-local) storage mechanism specified in
 * EIP-1153.
 *
 * Invariants (enforced by the EVM client using the storage):
 * - Each call to `checkpoint()` is followed by exactly one call to `commit()`
 *   or to `revert()`
 */
class TransientStorage
{
    struct JournalEntry
    {
        Address address;
        bytes32_t key;
        bytes32_t previous_value;
    };

public:
    TransientStorage() = default;

    TransientStorage(TransientStorage &&) = default;
    TransientStorage(TransientStorage const &) = default;
    TransientStorage &operator=(TransientStorage &&) = default;
    TransientStorage &operator=(TransientStorage const &) = default;

    /**
     * Get the current value set for a key in this address, or the zero word if
     * no value has previously been set.
     */
    bytes32_t get(Address const &addr, bytes32_t const &key) const;

    /**
     * Set a key-value mapping for this address, and store the previous value in
     * case we need to roll back on reverting a call.
     */
    void put(Address const &addr, bytes32_t const &key, bytes32_t const &value);

    /**
     * When a call succeeds, commit to its changes to storage by discarding the
     * checkpoint we set when beginning the call.
     */
    void commit();

    /**
     * When a call begins, set a checkpoint at the current journal state so that
     * we can roll back any changes made if the call reverts.
     */
    void checkpoint();

    /**
     * Apply saved storage changes in reverse, up to the previous checkpoint.
     */
    void revert();

private:
    std::vector<JournalEntry> journal_{};

    std::vector<std::size_t> checkpoints_{0};

    unordered_dense_map<Address, unordered_dense_map<bytes32_t, bytes32_t>>
        current_{};
};

MONAD_NAMESPACE_END
