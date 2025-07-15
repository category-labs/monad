#include <category/statesync/statesync_version.h>

// Modify when there are changes to the protocol

constexpr uint32_t MONAD_STATESYNC_VERSION = 1;

uint32_t monad_statesync_version()
{
    return MONAD_STATESYNC_VERSION;
}

bool monad_statesync_client_compatible(uint32_t const version)
{
    return version <= MONAD_STATESYNC_VERSION && version >= 1;
}
