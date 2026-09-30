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

#if !defined(MONAD_ZKVM_ZISK)
    #include_next <category/vm/interpreter/handler_policy.hpp>
#else
// On ZisK, pass the table base in a seventh register argument to avoid
// reloading it at each dispatch: the slots' base where the revision has them
// (dispatch_table, instruction_table.hpp), the table's otherwise.
    #define MONAD_VM_TBL_TYPE , void const *
    #define MONAD_VM_TBL_PARAM , void const *table_base
    #define MONAD_VM_TBL_ARG , table_base
    #define MONAD_VM_TABLE_REF (dispatch_table<traits>(table_base))
#endif
