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

#include <category/core/bytes.hpp>
#include <category/core/config.hpp>
#include <cstdint>

MONAD_NAMESPACE_BEGIN

/// Other EVM implementations do not emit consensus events like the Monad chain,
/// but emitting dummy versions reduces the difference for event consumers that
/// wait to see a particular commitment state (e.g., finalized) before acting.
void record_mock_consensus_events(
    bytes32_t const &block_id, uint64_t block_number);

MONAD_NAMESPACE_END
