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

#include <category/core/address.hpp>
#include <category/core/bytes.hpp>
#include <category/core/config.hpp>
#include <category/core/monad_exception.hpp>
#include <category/execution/ethereum/state3/state.hpp>
#include <category/execution/ethereum/trace/code_tracer.hpp>
#include <category/execution/ethereum/trace/state_trace_operations.hpp>
#include <category/vm/code.hpp>

#include <ankerl/unordered_dense.h>

MONAD_NAMESPACE_BEGIN

bool CodeTraceRunner::operator()(trace::state_trace::ReadCode const &op)
{
    bytes32_t const &code_hash = op.state.get_code_hash(op.address);
    if (code_hash == NULL_HASH) {
        return false;
    }
    auto const vcode = op.state.read_code(code_hash);
    MONAD_ASSERT_THROW(vcode, "Got null intercode object");
    codes.emplace(code_hash, vcode->intercode());
    return true;
}

MONAD_NAMESPACE_END
