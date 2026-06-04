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

// zkVM mirror — execute_transaction.cpp and execute_block_header.cpp only
// forward their ExecutionEventRecorder pointer on to the record_* no-ops in
// record_txn_events.hpp; neither ever dereferences it, so an incomplete type
// is enough. Declaring it here keeps the host header out of the guest build:
// that one pulls in event_recorder.h, whose inline
// monad_event_get_epoch_nanos() calls clock_gettime() — unavailable on bare
// metal.

#pragma once

#include <category/core/config.hpp>

MONAD_NAMESPACE_BEGIN

class ExecutionEventRecorder;

MONAD_NAMESPACE_END
