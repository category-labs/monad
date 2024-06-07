#include <monad/core/cpuset.h>

#include <stdlib.h>
#include <string.h>

#include <sched.h>

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
