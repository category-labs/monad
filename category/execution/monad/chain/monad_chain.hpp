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
#include <category/execution/ethereum/chain/chain.hpp>
#include <category/execution/monad/chain/monad_revision.h>

#include <evmc/evmc.h>

MONAD_NAMESPACE_BEGIN

inline constexpr size_t MAX_CODE_SIZE_MONAD_TWO = 128 * 1024;
inline constexpr size_t MAX_INITCODE_SIZE_MONAD_FOUR =
    2 * MAX_CODE_SIZE_MONAD_TWO;

struct BlockHeader;
struct Transaction;

struct MonadChain : Chain
{
    virtual evmc_revision
    get_revision(uint64_t block_number, uint64_t timestamp) const override;

    virtual Result<void> validate_output_header(
        BlockHeader const &input, BlockHeader const &output) const override;

    virtual uint64_t compute_gas_refund(
        uint64_t block_number, uint64_t timestamp, Transaction const &,
        uint64_t gas_remaining, uint64_t refund) const override;

    virtual monad_revision get_monad_revision(uint64_t timestamp) const = 0;

    virtual size_t
    get_max_code_size(uint64_t block_number, uint64_t timestamp) const override;

    virtual size_t get_max_initcode_size(
        uint64_t block_number, uint64_t timestamp) const override;

    virtual std::optional<evmc::Result> check_call_precompile(
        uint64_t block_number, uint64_t timestamp, State &,
        evmc_message const &) const override;

    virtual bool get_create_inside_delegated() const override;

    virtual bool get_p256_verify_enabled(
        uint64_t block_number, uint64_t timestamp) const override;

    virtual bool is_system_sender(Address const &) const override;
};

MONAD_NAMESPACE_END
