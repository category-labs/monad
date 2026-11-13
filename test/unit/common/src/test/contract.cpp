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

#include <category/core/byte_string.hpp>
#include <category/core/bytes.hpp>
#include <category/core/keccak.hpp>
#include <category/vm/code.hpp>

#include <monad/test/config.hpp>
#include <monad/test/contract.hpp>

MONAD_TEST_NAMESPACE_BEGIN

Contract::Contract(byte_string_view const code)
    : code{code}
    , hash{to_bytes(keccak256(code))}
    , icode{vm::make_shared_intercode(code.data(), code.size())}
{
}

MONAD_TEST_NAMESPACE_END
