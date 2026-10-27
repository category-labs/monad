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

// The inputs of domain `domain_chain_id` in one L1 block, from the block's
// header and the DomainHub.DomainRegistered, DomainTransactionSequenced,
// L1MessageRecorded and EncryptedL1MessageRecorded events in its receipts,
// in receipt and log order. Receipt blooms reject unrelated receipts before
// their logs are visited. Only the domain's events are decoded, so a
// malformed event of another domain never affects this one; a malformed
// event of the domain is an error.
Result<DomainInputs> scan_domain_inputs(
    BlockHeader const &l1_header, std::span<Receipt const>,
    Address const &domain_hub, uint64_t domain_chain_id);

MONAD_DOMAIN_NAMESPACE_END
