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

#include <cstdint>
#include <span>

#include <category/core/event/event_ring.h>
#include <category/core/event/test_event_ctypes.h>
#include <category/execution/ethereum/event/exec_event_ctypes.h>

struct monad_event_metadata;

#if defined(__clang__)
    #pragma GCC diagnostic push
    #pragma GCC diagnostic ignored "-Wc99-designator"
#endif

constexpr struct MetadataTableEntry
{
    uint8_t const (*schema_hash)[32];
    std::span<monad_event_metadata const> event_meta;
} MetadataTable[] = {
    [MONAD_EVENT_CONTENT_TYPE_NONE] =
        {
            nullptr,
            {},
        },
    [MONAD_EVENT_CONTENT_TYPE_TEST] =
        {
            &g_monad_test_event_schema_hash,
            std::span{g_monad_test_event_metadata},
        },
    [MONAD_EVENT_CONTENT_TYPE_EXEC] =
        {&g_monad_exec_event_schema_hash,
         std::span{g_monad_exec_event_metadata}},
};

#if defined(__clang__)
    #pragma GCC diagnostic pop
#endif
