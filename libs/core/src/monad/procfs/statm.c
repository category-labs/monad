#include <monad/core/cleanup.h>
#include <monad/core/likely.h>
#include <monad/procfs/statm.h>

#include <stdbool.h>
#include <stdio.h>

#include <unistd.h>

static long PAGESIZE = 0;

__attribute__((constructor)) static void monad_procfs_statm_init()
{
    PAGESIZE = sysconf(_SC_PAGESIZE);
}

bool monad_procfs_self_statm(
    long *const size, long *const resident, long *const shared)
{
    FILE *const fp [[gnu::cleanup(cleanup_fclose)]] =
        fopen("/proc/self/statm", "r");
    if (MONAD_UNLIKELY(!fp)) {
        return false;
    }

    int const result = fscanf(fp, "%ld %ld %ld", size, resident, shared);
    if (MONAD_UNLIKELY(result != 3)) {
        return false;
    }

    return true;
}

long monad_procfs_self_resident()
{
    long size, resident, shared;

    if (MONAD_UNLIKELY(!monad_procfs_self_statm(&size, &resident, &shared))) {
        return -1L;
    }

    return resident * PAGESIZE;
}
