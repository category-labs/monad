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
#include <category/core/bytes.hpp>
#include <category/execution/domain/config.hpp>
#include <category/execution/ethereum/core/transaction.hpp>

#include <cstdint>
#include <optional>
#include <vector>

MONAD_DOMAIN_NAMESPACE_BEGIN

// A domain block as derivation hands it to execution. It has no encoding and
// no id: it is handed on in memory, never stored or sent.
struct DerivedDomainBlock
{
    // Domain block height
    uint64_t number{};
    uint64_t l1_block_number{};
    // Copied from the L1 block.
    uint64_t timestamp{};
    bytes32_t prev_randao{};
    std::optional<uint64_t> slot_number{};
    std::vector<Transaction> transactions{};
    // Sender of each transaction; DOMAIN_SYSTEM_RELAYER for message deliveries.
    std::vector<Address> senders{};

    friend bool operator==(
        DerivedDomainBlock const &, DerivedDomainBlock const &) = default;
};

MONAD_DOMAIN_NAMESPACE_END
