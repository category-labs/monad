#pragma once

#include <monad/evm/config.hpp>

MONAD_EVM_NAMESPACE_BEGIN

// EIP-2200
enum class StorageStatus
{
    // catch-all status
    Assigned = 0,

    // 0 -> 0 -> Z
    Added = 1,

    // X -> X -> 0
    Deleted = 2,

    // X -> X -> Z
    Modified = 3,

    // X -> 0 -> Z
    DeletedThenAdded = 4,

    // X -> Y -> 0
    ModifiedThenDeleted = 5,

    // X -> 0 -> X
    DeletedThenRestored = 6,

    // 0 -> Y -> 0
    AddedThenDeleted = 7,

    // X -> Y -> X
    ModifiedThenRestored = 8
};

MONAD_EVM_NAMESPACE_END
