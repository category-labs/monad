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

#pragma once

/**
 * @file
 *
 * Definitions of events used with the TEST event ring
 */

#include <stddef.h>
#include <stdint.h>

#include <category/core/event/event_def.h>
#include <category/core/event/event_metadata.h>

#ifdef __cplusplus
extern "C"
{
#endif

/// Each type of event is assigned a unique value in this enumeration
enum monad_test_event : uint16_t
{
    MONAD_TEST_EVENT_NONE,
    MONAD_TEST_EVENT_RECORD_ERROR,
    MONAD_TEST_EVENT_COUNTER,
    MONAD_TEST_EVENT_VLT,
};

/// Event payload for MONAD_TEST_EVENT_COUNTER
struct monad_test_event_counter
{
    uint8_t writer_id;
    uint64_t counter;
};

/// Event payload for MONAD_TEST_EVENT_VLT
struct monad_test_event_vlt
{
    uint32_t vlt_1_length;
    uint32_t vlt_2_length;
};

extern struct monad_event_metadata const g_monad_test_event_metadata[4];
extern uint8_t const g_monad_test_event_schema_hash[32];

constexpr char MONAD_EVENT_DEFAULT_TEST_FILE_NAME[] = "event-recorder-test";

constexpr size_t MONAD_TEST_EVENT_VERSION_COUNT = 4;
extern struct monad_event_content_version_table_entry const
    g_monad_test_event_versions[MONAD_TEST_EVENT_VERSION_COUNT];

static struct monad_event_content_version_table const
    g_monad_test_event_version_table = {
        .entries = g_monad_test_event_versions,
        .count = MONAD_TEST_EVENT_VERSION_COUNT};

#ifdef __cplusplus
} // extern "C"
#endif
