// Copyright (C) 2025-26 Category Labs, Inc.
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

#include <stdint.h>
#include <string.h>

#include <category/core/event/event_def.h>

char const *g_monad_event_content_type_names[MONAD_EVENT_CONTENT_TYPE_COUNT] = {
    [MONAD_EVENT_CONTENT_TYPE_NONE] = "none",
    [MONAD_EVENT_CONTENT_TYPE_TEST] = "test",
    [MONAD_EVENT_CONTENT_TYPE_EXEC] = "exec",
};

struct monad_event_content_version const *monad_event_content_lookup_version(
    uint8_t const (*const schema_hash)[32],
    struct monad_event_content_version_table const version_table)
{
    for (size_t i = 0; i < version_table.count; ++i) {
        struct monad_event_content_version_table_entry const *const e =
            &version_table.entries[i];
        if (memcmp(e->schema_hash, schema_hash, sizeof e->schema_hash) == 0) {
            return &e->version;
        }
    }
    return nullptr;
}
