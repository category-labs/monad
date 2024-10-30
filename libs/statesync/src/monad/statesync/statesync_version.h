#pragma once

#include <stdint.h>

#ifdef __cplusplus
extern "C"
{
#endif

uint32_t monad_statesync_version();

bool monad_statesync_client_compatible(uint32_t version);

#ifdef __cplusplus
}
#endif
