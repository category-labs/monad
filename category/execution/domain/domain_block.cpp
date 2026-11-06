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

#include <category/execution/domain/domain_block.hpp>

#include <category/core/bytes.hpp>
#include <category/core/keccak.hpp>
#include <category/execution/domain/config.hpp>
#include <category/execution/domain/rlp/domain_block_rlp.hpp>

MONAD_DOMAIN_NAMESPACE_BEGIN

bytes32_t domain_block_id(DomainBlockHeader const &header)
{
    return to_bytes(keccak256(rlp::encode_domain_block_header(header)));
}

MONAD_DOMAIN_NAMESPACE_END
