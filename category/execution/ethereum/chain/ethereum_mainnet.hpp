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

#include <cstdint>
#include <span>

MONAD_NAMESPACE_BEGIN

struct BlockHeader;
struct Receipt;
struct Transaction;

namespace eth_forks
{
    inline constexpr uint64_t OSAKA_ACTIVATION_TIMESTAMP = 1764798551;
    inline constexpr uint64_t PRAGUE_ACTIVATION_TIMESTAMP = 1746612311;
    inline constexpr uint64_t CANCUN_ACTIVATION_TIMESTAMP = 1710338135;
    inline constexpr uint64_t SHANGHAI_ACTIVATION_TIMESTAMP = 1681338455;

    inline constexpr uint64_t PARIS_ACTIVATION_BLOCK_NUMBER = 15537394;
    inline constexpr uint64_t LONDON_ACTIVATION_BLOCK_NUMBER = 12965000;
    inline constexpr uint64_t BERLIN_ACTIVATION_BLOCK_NUMBER = 12244000;

    // Mainnet BPO activation times and blob parameters are canonicalized in
    // EIP-8134 and EIP-8135. BPO scheduling itself is defined by EIP-7892.
    inline constexpr uint64_t BPO1_ACTIVATION_TIMESTAMP = 1765290071;
    inline constexpr uint64_t BPO2_ACTIVATION_TIMESTAMP = 1767747671;
}

namespace constants
{
    // Replay support policy: the earliest supported fork is Berlin, so
    // blocks before its activation cannot be executed. The revision-valued
    // counterpart, EARLIEST_SUPPORTED_EVM_FORK, lives in vm/evm/traits.hpp.
    inline constexpr uint64_t EARLIEST_SUPPORTED_ETH_BLOCK_NUMBER =
        eth_forks::BERLIN_ACTIVATION_BLOCK_NUMBER;
}

inline constexpr size_t MAX_CODE_SIZE_EIP170 = 24 * 1024; // 0x6000
inline constexpr size_t MAX_INITCODE_SIZE_EIP3860 =
    2 * MAX_CODE_SIZE_EIP170; // 0xC000

struct EthereumMainnet : Chain
{
    virtual uint256_t get_chain_id() const override;

    virtual monad_eth_revision
    get_revision(uint64_t block_number, uint64_t timestamp) const override;

    virtual BlobSchedule get_blob_schedule(uint64_t timestamp) const override;

    virtual GenesisState get_genesis_state() const override;
};

MONAD_NAMESPACE_END
