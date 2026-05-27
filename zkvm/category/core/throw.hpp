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

#pragma once

// zkVM mirror: exceptions are disabled (-fno-exceptions) on the bare-metal
// zkVM build, so MONAD_THROW falls back to zkvm_halt(1), which must always
// be marked as noreturn to preserve throw control flow behavior.
#include <zkvm/core/zkvm_halt.h>

#define MONAD_THROW(exc, msg) zkvm_halt(1)
