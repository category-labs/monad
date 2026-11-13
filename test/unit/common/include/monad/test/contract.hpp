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

#include <category/core/byte_string.hpp>
#include <category/core/bytes.hpp>
#include <category/vm/code.hpp>

#include <monad/test/config.hpp>

MONAD_TEST_NAMESPACE_BEGIN

/// Contract bytecode bundled with the two values derived from it that tests
/// need to install it into state: its keccak256 hash and its intercode.
struct Contract
{
    byte_string code;
    bytes32_t hash;
    vm::SharedIntercode icode;

    explicit Contract(byte_string_view code);
};

MONAD_TEST_NAMESPACE_END
