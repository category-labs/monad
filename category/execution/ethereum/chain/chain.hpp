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

#include <category/core/bytes.hpp>
#include <category/core/config.hpp>
#include <category/core/int.hpp>
#include <category/core/result.hpp>
#include <category/execution/ethereum/chain/genesis_state.hpp>

#include <evmc/evmc.h>

MONAD_NAMESPACE_BEGIN

struct BlockHeader;
struct Receipt;
struct Transaction;

struct Chain
{
    virtual ~Chain() = default;

    virtual uint256_t get_chain_id() const = 0;

    virtual evmc_revision
    get_revision(uint64_t block_number, uint64_t timestamp) const = 0;

    virtual Result<void> static_validate_header(BlockHeader const &) const;

    virtual Result<void> validate_output_header(
        BlockHeader const &input, BlockHeader const &output) const = 0;

    virtual uint64_t compute_gas_refund(
        uint64_t block_number, uint64_t timestamp, Transaction const &,
        uint64_t gas_remaining, uint64_t refund) const = 0;

    virtual size_t
    get_max_code_size(uint64_t block_number, uint64_t timestamp) const = 0;

    virtual size_t
    get_max_initcode_size(uint64_t block_number, uint64_t timestamp) const = 0;

    virtual GenesisState get_genesis_state() const = 0;

    virtual bool get_create_inside_delegated() const = 0;

    virtual bool get_p256_verify_enabled(
        uint64_t block_number, uint64_t timestamp) const = 0;
};

MONAD_NAMESPACE_END
