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

#include <category/core/config.hpp>
#include <category/core/event/owned_event_ring.hpp>
#include <category/execution/ethereum/event/exec_event_recorder.hpp>

#include <memory>

MONAD_NAMESPACE_BEGIN

std::unique_ptr<OwnedEventRing> g_exec_event_ring;
std::unique_ptr<ExecutionEventRecorder> g_exec_event_recorder;

MONAD_NAMESPACE_END
