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
 * Interface between `monad` and the execution event recording infrastructure
 * in libmonad_execution
 */

#include <category/core/config.hpp>

#include <cstddef>
#include <cstdint>
#include <expected>
#include <string>
#include <string_view>

MONAD_NAMESPACE_BEGIN

// clang-format off

struct EventRingConfig
{
    std::string event_ring_spec; ///< File name or path to shared memory file
    uint8_t descriptors_shift;   ///< Descriptor capacity = 2^descriptors_shift
    uint8_t payload_buf_shift;   ///< Payload buffer size = 2^payload_buf_shift
};

// clang-format on

// General advice for setting the default ring parameters below: the average
// event payload length (at the time of this writing) is about 200 bytes, close
// to 256 (2^8). Thus, the default payload buffer shift is equal to the default
// descriptor shift plus 8. At current rates a block generates about 1MiB of
// event data on average, so the below size keeps a few minutes worth of
// history and gives a large amount of slack for slow consumers. These values
// are likely to change in the future, you can view current numbers using the
// `eventcap execstats` subcommand
constexpr uint8_t DEFAULT_EXEC_RING_DESCRIPTORS_SHIFT = 21;
constexpr uint8_t DEFAULT_EXEC_RING_PAYLOAD_BUF_SHIFT = 29;

/// Parse an event ring configuration string of the form
/// `<file-path>[:<ring-shift>:<payload-buffer-shift>]`; if a parse
/// error occurs, return a string describing the error
std::expected<EventRingConfig, std::string>
    try_parse_event_ring_config(std::string_view);

/// Initialize the global recorder object for the execution event ring (an
/// object inside the libmonad_execution_ethereum object library) with the
/// given configuration options
int init_execution_event_recorder(EventRingConfig);

MONAD_NAMESPACE_END
