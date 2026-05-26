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

#include <category/core/config.hpp>

MONAD_NAMESPACE_BEGIN

// Populate the mpt::state_machine_kind registry with every concrete
// StateMachine subclass that lives under category/execution/ethereum/db.
// Must run once at process start before any mpt::Db is constructed via
// the metadata-driven Db(OnDiskDbConfig const &) ctor; otherwise
// create_state_machine() aborts at open time.
//
// Idempotent — re-registering the same kind overwrites the prior factory.
void register_ethereum_state_machines();

MONAD_NAMESPACE_END
