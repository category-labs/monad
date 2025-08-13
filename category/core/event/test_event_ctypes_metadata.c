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

#include <stddef.h>
#include <stdint.h>

#include <category/core/event/event_metadata.h>
#include <category/core/event/test_event_ctypes.h>

#ifdef __cplusplus
extern "C"
{
#endif

struct monad_event_metadata const g_monad_test_event_metadata[2] = {

    [MONAD_TEST_EVENT_NONE] =
        {.event_type = MONAD_TEST_EVENT_NONE,
         .c_name = "NONE",
         .description = "reserved code so that 0 remains invalid"},

    [MONAD_TEST_EVENT_COUNTER] =
        {.event_type = MONAD_TEST_EVENT_COUNTER,
         .c_name = "TEST_COUNTER",
         .description = "A special event emitted only by the test suite"},

};

uint8_t const g_monad_test_event_schema_hash[32] = {};

#ifdef __cplusplus
} // extern "C"
#endif
