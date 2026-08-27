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

// Host settings of the interpreter handlers. Guest builds override them through
// their shadow header.

// All dispatching handlers must use MONAD_VM_TBL_PARAM and MONAD_VM_TBL_ARG,
// which pass no table base here: handlers read the table directly.
#define MONAD_VM_TBL_TYPE
#define MONAD_VM_TBL_PARAM
#define MONAD_VM_TBL_ARG
#define MONAD_VM_TABLE_REF instruction_table<traits>
