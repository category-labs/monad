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

#include <category/core/address.hpp>
#include <category/core/result.hpp>
#include <category/execution/domain/config.hpp>
#include <category/execution/domain/inputs.hpp>
#include <category/execution/ethereum/core/block.hpp>
#include <category/execution/ethereum/core/receipt.hpp>

#include <cstdint>
#include <span>

MONAD_DOMAIN_NAMESPACE_BEGIN

// Whether the L1 block of `l1_header` can hold inputs of domain
// `domain_chain_id`, by the header's logs bloom alone. False means it holds
// none, so its receipts need not be read; true can be a false positive.
bool may_have_domain_inputs(
    BlockHeader const &l1_header, Address const &domain_hub,
    uint64_t domain_chain_id);

// The inputs of domain `domain_chain_id` in one L1 block, from the block's
// header and the DomainHub events in its receipts, in log order. A malformed
// event of the domain is an error; events of other domains are ignored.
Result<DomainInputs> scan_domain_inputs(
    BlockHeader const &l1_header, std::span<Receipt const>,
    Address const &domain_hub, uint64_t domain_chain_id);

MONAD_DOMAIN_NAMESPACE_END
