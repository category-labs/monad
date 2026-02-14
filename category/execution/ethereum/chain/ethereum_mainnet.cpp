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

#include <category/execution/ethereum/chain/ethereum_mainnet.hpp>

#include <category/core/config.hpp>
#include <category/core/int.hpp>
#include <category/core/likely.h>
#include <category/core/result.hpp>
#include <category/core/unaligned.hpp>
#include <category/execution/ethereum/chain/ethereum_mainnet_alloc.hpp>
#include <category/execution/ethereum/core/block.hpp>
#include <category/execution/ethereum/core/fmt/bytes_fmt.hpp>
#include <category/execution/ethereum/dao.hpp>
#include <category/execution/ethereum/execute_transaction.hpp>
#include <category/execution/ethereum/precompiles.hpp>
#include <category/execution/ethereum/state3/state.hpp>
#include <category/execution/ethereum/validate_block.hpp>
#include <category/execution/ethereum/validate_transaction.hpp>
#include <category/vm/evm/switch_traits.hpp>

#include <evmc/evmc.h>

#include <bit>
#include <boost/outcome/config.hpp>
#include <boost/outcome/success_failure.hpp>
#include <boost/outcome/try.hpp>

#include <limits>

MONAD_NAMESPACE_BEGIN

using BOOST_OUTCOME_V2_NAMESPACE::success;

uint256_t EthereumMainnet::get_chain_id() const
{
    return 1;
};

evmc_revision EthereumMainnet::get_revision(
    uint64_t const block_number, uint64_t const timestamp) const
{
    // TODO: update to include Prague once we can replay those blocks

    if (MONAD_LIKELY(timestamp >= 1710338135)) {
        return EVMC_CANCUN;
    }
    else if (timestamp >= 1681338455) {
        return EVMC_SHANGHAI;
    }
    else if (block_number >= 15537394) {
        return EVMC_PARIS;
    }
    else if (block_number >= 12965000) {
        return EVMC_LONDON;
    }
    else if (block_number >= 12244000) {
        return EVMC_BERLIN;
    }
    else if (block_number >= 9069000) {
        return EVMC_ISTANBUL;
    }
    else if (block_number >= 7280000) {
        return EVMC_PETERSBURG;
    }
    else if (block_number >= 4370000) {
        return EVMC_BYZANTIUM;
    }
    else if (block_number >= 2675000) {
        return EVMC_SPURIOUS_DRAGON;
    }
    else if (block_number >= 2463000) {
        return EVMC_TANGERINE_WHISTLE;
    }
    else if (block_number >= 1150000) {
        return EVMC_HOMESTEAD;
    }
    return EVMC_FRONTIER;
}

Result<void>
EthereumMainnet::static_validate_header(BlockHeader const &header) const
{
    // EIP-779
    if (MONAD_UNLIKELY(
            header.number >= dao::dao_block_number &&
            header.number <= dao::dao_block_number + 9 &&
            header.extra_data != dao::extra_data)) {
        return BlockError::WrongDaoExtraData;
    }
    return success();
}

GenesisState EthereumMainnet::get_genesis_state() const
{
    // byteswap for nonce storage requires little-endian
    static_assert(
        std::endian::native == std::endian::little,
        "get_genesis_state requires little-endian for byteswap");

    BlockHeader header;
    header.difficulty = 17179869184;
    header.gas_limit = 5000;
    unaligned_store(header.nonce.data(), std::byteswap(uint64_t{66}));
    header.extra_data = evmc::from_hex("0x11bbe8db4e347b4e8c937c1c8370e4b5ed33a"
                                       "db3db69cbdb7a38e1e50b1b82fa")
                            .value();
    return {header, ETHEREUM_MAINNET_ALLOC};
}

Result<void> EthereumMainnet::validate_transaction(
    uint64_t const block_number, uint64_t const timestamp,
    Transaction const &tx, Address const &sender, State &state,
    uint256_t const &, std::span<std::optional<Address> const>) const
{
    evmc_revision const rev = get_revision(block_number, timestamp);
    return ::monad::validate_transaction(rev, tx, sender, state);
}

MONAD_NAMESPACE_END
