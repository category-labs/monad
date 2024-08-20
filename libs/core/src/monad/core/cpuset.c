#include <monad/core/assert.h>
#include <monad/core/cpuset.h>

#include <stdlib.h>
#include <string.h>

#include <sched.h>
#include <sys/sysinfo.h>

cpu_set_t monad_parse_cpuset(char *const s)
{
    cpu_set_t set;

    CPU_ZERO(&set);

    // TODO error handling
    char *state = NULL;
    char *tok = strtok_r(s, ",", &state);
    while (tok) {
        unsigned m, n;
        char *tok2 = strchr(tok, '-');
        if (tok2) {
            *tok2 = '\0';
            ++tok2;
        }
        m = (unsigned)(atoi(tok));
        if (tok2) {
            n = (unsigned)(atoi(tok2));
        }
        else {
            n = m;
        }
        for (unsigned i = m; i <= n; ++i) {
            CPU_SET(i, &set);
        }
        tok = strtok_r(NULL, ",", &state);
    }

    return set;
}

cpu_set_t monad_cpuset_from_cpu(int cpu)
{
    MONAD_ASSERT(cpu >= 0);
    cpu_set_t set;
    CPU_ZERO(&set);
    CPU_SET((unsigned)cpu, &set);
    return set;
}

int monad_alloc_cpu(cpu_set_t *input_set)
{
    int num_cpus = get_nprocs();
    MONAD_ASSERT(num_cpus >= 0);
    for (unsigned i = 0; i < (unsigned)num_cpus; ++i) {
        if (CPU_ISSET(i, input_set)) {
            CPU_CLR(i, input_set);
            return (int)i;
        }
    }
    return -1;
}
