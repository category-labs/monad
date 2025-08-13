// Copyright (C) 2025 Category Labs, Inc.
//
// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with this program.  If not, see <http://www.gnu.org/licenses/>.

#include <category/core/cpuset.h>

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
