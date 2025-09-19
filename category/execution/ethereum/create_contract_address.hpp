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

#include <category/core/bytes.hpp>
#include <category/execution/ethereum/core/address.hpp>

#include <ethash/hash_types.hpp>

MONAD_NAMESPACE_BEGIN

Address create_contract_address(Address const &from, uint64_t const nonce);
Address create2_contract_address(
    Address const &from, bytes32_t const &zeta,
    ethash::hash256 const &code_hash);

MONAD_NAMESPACE_END
