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
#include <category/execution/ethereum/chain/chain.hpp>
#include <category/execution/ethereum/chain/genesis_state.hpp>

#include <evmc/evmc.h>

MONAD_NAMESPACE_BEGIN

struct BlockHeader;
struct Receipt;
struct Transaction;

inline constexpr size_t MAX_CODE_SIZE_EIP170 = 24 * 1024; // 0x6000
inline constexpr size_t MAX_INITCODE_SIZE_EIP3860 =
    2 * MAX_CODE_SIZE_EIP170; // 0xC000

struct EthereumMainnet : Chain
{
    virtual uint256_t get_chain_id() const override;

    virtual evmc_revision
    get_revision(uint64_t block_number, uint64_t timestamp) const override;

    virtual Result<void>
    static_validate_header(BlockHeader const &) const override;

    virtual Result<void> validate_output_header(
        BlockHeader const &input, BlockHeader const &output) const override;

    virtual GenesisState get_genesis_state() const override;

    virtual Result<void> validate_transaction(
        uint64_t block_number, uint64_t timestamp, Transaction const &,
        Address const &sender, State &, uint256_t const &base_fee_per_gas,
        std::vector<std::optional<Address>> const &authorities) const override;
};

MONAD_NAMESPACE_END
