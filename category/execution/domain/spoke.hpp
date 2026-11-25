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
#include <category/core/byte_string.hpp>
#include <category/execution/domain/config.hpp>

#include <cstdint>

MONAD_NAMESPACE_BEGIN

class State;

MONAD_NAMESPACE_END

MONAD_DOMAIN_NAMESPACE_BEGIN

// The address of the DomainSpoke of every private domain. A domain's genesis
// state holds its spoke: see PROTOCOL.md in category-labs/monad-domains.
inline constexpr Address DOMAIN_SPOKE{
    0x000000000000000000446f6d61696e53706f6b65_address};

// The code of the spoke of domain `domain_chain_id` of the L1 `l1_chain_id`
// whose DomainHub is `hub`: what DomainSpoke's constructor deploys for them.
byte_string domain_spoke_code(
    uint64_t domain_chain_id, uint64_t l1_chain_id, Address const &hub);

// Puts that spoke into `state`, which must not have it.
void deploy_domain_spoke(
    State &, uint64_t domain_chain_id, uint64_t l1_chain_id,
    Address const &hub);

MONAD_DOMAIN_NAMESPACE_END
