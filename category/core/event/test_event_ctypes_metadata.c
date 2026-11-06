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

#include <category/core/event/event_def.h>
#include <category/core/event/event_metadata.h>
#include <category/core/event/test_event_ctypes.h>

#ifdef __cplusplus
extern "C"
{
#endif

struct monad_event_metadata const g_monad_test_event_metadata[4] = {

    [MONAD_TEST_EVENT_NONE] =
        {.event_type = MONAD_TEST_EVENT_NONE,
         .c_name = "NONE",
         .description = "Reserved code so that 0 remains invalid"},

    [MONAD_TEST_EVENT_RECORD_ERROR] =
        {.event_type = MONAD_TEST_EVENT_RECORD_ERROR,
         .c_name = "RECORD_ERROR",
         .description = "Reserved event type used for recording errors"},

    [MONAD_TEST_EVENT_COUNTER] =
        {.event_type = MONAD_TEST_EVENT_COUNTER,
         .c_name = "TEST_COUNTER",
         .description = "A test suite event that counts"},

    [MONAD_TEST_EVENT_VLT] =
        {.event_type = MONAD_TEST_EVENT_VLT,
         .c_name = "TEST_VLT",
         .description =
             "A test suite event that records variable-length trailing arrays"},

};

uint8_t const g_monad_test_event_schema_hash[32] = {
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01,
};

struct monad_event_content_version_table_entry const
    g_monad_test_event_versions[MONAD_TEST_EVENT_VERSION_COUNT] = {
        [0] = {.version = {0, 0}, .schema_hash = {}},
        [1] = {.version = {0, 1}, .schema_hash = {0x00, 0x00, 0x00, 0x00, 0x00,
                                                  0x00, 0x00, 0x00, 0x00, 0x00,
                                                  0x00, 0x00, 0x00, 0x00, 0x00,
                                                  0x00, 0x00, 0x00, 0x00, 0x00,
                                                  0x00, 0x00, 0x00, 0x00, 0x00,
                                                  0x00, 0x00, 0x00, 0x00, 0x00,
                                                  0x00, 0x01}},
        [2] = {.version = {0, 2}, .schema_hash = {0x00, 0x00, 0x00, 0x00, 0x00,
                                                  0x00, 0x00, 0x00, 0x00, 0x00,
                                                  0x00, 0x00, 0x00, 0x00, 0x00,
                                                  0x00, 0x00, 0x00, 0x00, 0x00,
                                                  0x00, 0x00, 0x00, 0x00, 0x00,
                                                  0x00, 0x00, 0x00, 0x00, 0x00,
                                                  0x00, 0x02}},
        [3] = {.version = {1, 0}, .schema_hash = {0x00, 0x00, 0x00, 0x00, 0x00,
                                                  0x00, 0x00, 0x00, 0x00, 0x00,
                                                  0x00, 0x00, 0x00, 0x00, 0x00,
                                                  0x00, 0x00, 0x00, 0x00, 0x00,
                                                  0x00, 0x00, 0x00, 0x00, 0x00,
                                                  0x00, 0x00, 0x00, 0x00, 0x00,
                                                  0x01, 0x00}},
};

#ifdef __cplusplus
} // extern "C"
#endif
