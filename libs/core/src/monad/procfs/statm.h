#pragma once

#include <stdbool.h>

#ifdef __cplusplus
extern "C"
{
#endif

bool monad_procfs_self_statm(long *size, long *resident, long *shared);

long monad_procfs_self_resident();

#ifdef __cplusplus
}
#endif
