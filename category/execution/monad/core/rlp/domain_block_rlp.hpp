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
#include <category/core/result.hpp>
#include <category/core/rlp/config.hpp>
#include <category/execution/monad/core/domain_block.hpp>

MONAD_RLP_NAMESPACE_BEGIN

// ProposedDomainHeader = [domain_chain_id, number, l1_block_number,
//     l1_block_id, timestamp, mix_hash, gas_limit, base_fee_per_gas,
//     transactions_root]
byte_string encode_proposed_domain_header(ProposedDomainHeader const &);
Result<ProposedDomainHeader> decode_proposed_domain_header(byte_string_view &);

// DomainBlock = [header, [transactions, ommers, withdrawals]], where
// transactions are encoded as in an Ethereum block body and ommers and
// withdrawals are always empty lists.
byte_string encode_domain_block(DomainBlock const &);
Result<DomainBlock> decode_domain_block(byte_string_view &);

MONAD_RLP_NAMESPACE_END
