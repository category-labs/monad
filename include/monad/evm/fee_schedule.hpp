#pragma once

#include <monad/evm/config.hpp>
#include <monad/evm/opcodes.hpp>
#include <monad/evm/revision.hpp>
#include <monad/evm/storage_status.hpp>
#include <monad/evm/words.hpp>

#include <cstdint>

MONAD_EVM_NAMESPACE_BEGIN

// Appendix G

// G_zero
constexpr auto zero_cost = 0;

// G_jumpdest
constexpr auto jumpdest_cost = 1;

// G_base
constexpr auto base_cost = 2;

// G_verylow
constexpr auto very_low_cost = 3;

// G_low
constexpr auto low_cost = 5;

// G_mid
constexpr auto mid_cost = 8;

// G_high
constexpr auto high_cost = 10;

// G_warmaccess
template <Revision rev>
constexpr uint64_t warm_access_cost()
{
    if constexpr (rev < Revision::Istanbul) {
        return 200;
    }
    else if constexpr (rev == Revision::Istanbul) {
        return 800;
    }
    else if constexpr (rev >= Revision::Berlin) {
        return 100;
    }
}

// G_coldaccountaccess
template <Revision rev>
constexpr uint64_t cold_account_access_cost()
{
    if constexpr (rev >= Revision::Berlin) {
        return 2600;
    }
}

// G_coldsload
template <Revision rev>
constexpr uint64_t cold_sload_cost()
{
    if constexpr (rev >= Revision::Berlin) {
        return 2100;
    }
}

// G_sset
constexpr uint64_t sset_cost = 20000;

template <Revision rev>
constexpr uint64_t sreset_cost()
{
    if constexpr (rev < Revision::Berlin) {
        return 5000;
    }
    else if constexpr (rev >= Revision::Berlin) {
        return 5000 - cold_sload_cost<rev>();
    }
}

// R_sclear
template <Revision rev>
constexpr uint64_t sclear_refund()
{
    if constexpr (rev < Revision::London) {
        return 15000;
    }
    else if constexpr (rev >= Revision::London) {
        return 4800;
    }
}

// G_selfdestruct
constexpr auto selfdestruct_cost = 5000;

// G_create
constexpr auto create_cost = 32000;

// G_callvalue
constexpr auto call_value_cost = 9000;

// G_callstipend
constexpr auto call_stipend = 2300;

// G_newaccount
constexpr auto new_account_cost = 25000;

// G_exp
constexpr auto exp_cost = 10;

// G_memory
constexpr auto memory_cost = 3;

// G_logtopic
constexpr auto log_topic_cost = 375;

// G_keccak256
constexpr auto keccak256_cost = 30;

// G_keccak256word
constexpr auto keccak256_cost_per_word = 6;

// G_copy
constexpr auto copy_cost_per_word = 3;

// Helpers

template <Revision rev>
constexpr auto additional_cold_account_access_cost =
    cold_account_access_cost<rev>() - warm_access_cost<rev>();

template <Revision rev>
constexpr auto additional_cold_sload_cost =
    cold_sload_cost<rev>() - warm_access_cost<rev>();

template <Revision rev>
constexpr uint64_t sstore_cost(StorageStatus const status)
{
    if constexpr (rev < Revision::Constantinople) {
        switch (status) {
        case StorageStatus::Added:
        case StorageStatus::DeletedThenAdded:
        case StorageStatus::DeletedThenRestored:
            return sset_cost;
        case StorageStatus::Deleted:
        case StorageStatus::Modified:
        case StorageStatus::Assigned:
        case StorageStatus::ModifiedThenDeleted:
        case StorageStatus::AddedThenDeleted:
        case StorageStatus::ModifiedThenRestored:
            return sreset_cost<rev>();
        }
    }
    else {
        switch (status) {
        case StorageStatus::Assigned:
        case StorageStatus::DeletedThenAdded:
        case StorageStatus::ModifiedThenDeleted:
        case StorageStatus::DeletedThenRestored:
        case StorageStatus::AddedThenDeleted:
        case StorageStatus::ModifiedThenRestored:
            return warm_access_cost<rev>();
        case StorageStatus::Added:
            return sset_cost;
        case StorageStatus::Deleted:
        case StorageStatus::Modified:
            return sreset_cost<rev>();
        }
    }
    MONAD_ASSERT(false);
}

template <Revision rev>
constexpr int64_t sstore_refund(StorageStatus const status)
{
    if constexpr (rev < Revision::Constantinople) {
        switch (status) {
        case StorageStatus::Deleted:
        case StorageStatus::ModifiedThenDeleted:
        case StorageStatus::AddedThenDeleted:
            return sclear_refund<rev>();
        case StorageStatus::Added:
        case StorageStatus::DeletedThenAdded:
        case StorageStatus::DeletedThenRestored:
        case StorageStatus::Modified:
        case StorageStatus::Assigned:
        case StorageStatus::ModifiedThenRestored:
            return 0;
        }
    }
    else {
        static_assert(
            sclear_refund<rev>() <= std::numeric_limits<int64_t>::max());
        static_assert(
            sreset_cost<rev>() <= std::numeric_limits<int64_t>::max());
        static_assert(
            warm_access_cost<rev>() <= std::numeric_limits<int64_t>::max());
        switch (status) {
        case StorageStatus::Assigned:
        case StorageStatus::Added:
        case StorageStatus::Modified:
            return 0;
        case StorageStatus::Deleted:
        case StorageStatus::ModifiedThenDeleted:
            return sclear_refund<rev>();
        case StorageStatus::DeletedThenAdded:
            return -static_cast<int64_t>(sclear_refund<rev>());
        case StorageStatus::DeletedThenRestored:
            return static_cast<int64_t>(
                sreset_cost<rev>() - warm_access_cost<rev>() -
                sclear_refund<rev>());
        case StorageStatus::AddedThenDeleted:
            return sset_cost - warm_access_cost<rev>();
        case StorageStatus::ModifiedThenRestored:
            return sreset_cost<rev>() - warm_access_cost<rev>();
        }
    }
    MONAD_ASSERT(false);
}

constexpr uint64_t copy_cost(size_t const n)
{
    return round_up_bytes_to_words(n) * copy_cost_per_word;
}

MONAD_EVM_NAMESPACE_END
