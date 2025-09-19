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

#include <category/core/config.hpp>
#include <category/core/likely.h>
#include <category/core/result.hpp>
#include <category/execution/ethereum/chain/ethereum_mainnet.hpp>
#include <category/execution/ethereum/core/block.hpp>
#include <category/execution/ethereum/state3/state.hpp>
#include <category/execution/ethereum/transaction_gas.hpp>
#include <category/execution/ethereum/validate_block.hpp>
#include <category/execution/monad/chain/monad_chain.hpp>
#include <category/execution/monad/reserve_balance.h>

#include <algorithm>

MONAD_ANONYMOUS_NAMESPACE_BEGIN

bool dipped_into_reserve(
    monad_revision const monad_rev, evmc_revision const rev,
    Address const &sender, Transaction const &tx,
    uint256_t const &base_fee_per_gas, uint64_t const i,
    MonadChainContext const &ctx, State &state)
{
    MONAD_ASSERT(i < ctx.senders.size());
    MONAD_ASSERT(i < ctx.authorities.size());
    MONAD_ASSERT(ctx.senders.size() == ctx.authorities.size());

    uint256_t const gas_fees =
        uint256_t{tx.gas_limit} * gas_price(rev, tx, base_fee_per_gas);
    auto const &orig = state.original();
    for (auto const &[addr, stack] : state.current()) {
        MONAD_ASSERT(orig.contains(addr));
        std::optional<Account> const &orig_account = orig.at(addr).account_;
        bytes32_t const orig_code_hash = orig_account.has_value()
                                             ? orig_account.value().code_hash
                                             : NULL_HASH;

        // Skip if not EOA
        if (orig_code_hash != NULL_HASH) {
            vm::SharedIntercode const intercode =
                state.read_code(orig_code_hash)->intercode();
            if (!monad::vm::evm::is_delegated(
                    {intercode->code(), intercode->size()})) {
                continue;
            }
        }

        // Check if dipped into reserve
        std::optional<uint256_t> const violation_threshold =
            [&] -> std::optional<uint256_t> {
            uint256_t const orig_balance =
                orig_account.has_value() ? orig_account.value().balance : 0;
            uint256_t const reserve =
                std::min(get_max_reserve(monad_rev, addr), orig_balance);
            if (addr == sender) {
                if (gas_fees > reserve) { // must be dipping
                    return std::nullopt;
                }
                return reserve - gas_fees;
            }
            return reserve;
        }();
        std::optional<Account> const &curr_account = stack.recent().account_;
        uint256_t const curr_balance =
            curr_account.has_value() ? curr_account.value().balance : 0;
        if (!violation_threshold.has_value() ||
            curr_balance < violation_threshold.value()) {
            if (addr == sender) {
                if (!can_sender_dip_into_reserve(
                        sender, i, orig_code_hash, ctx)) {
                    MONAD_ASSERT(
                        violation_threshold.has_value(),
                        "gas fee greater than reserve for non-dipping "
                        "transaction");
                    return true;
                }
                // Skip if allowed to dip into reserve
            }
            else {
                MONAD_ASSERT(violation_threshold.has_value());
                return true;
            }
        }
    }
    return false;
}

MONAD_ANONYMOUS_NAMESPACE_END

MONAD_NAMESPACE_BEGIN

using BOOST_OUTCOME_V2_NAMESPACE::success;

evmc_revision MonadChain::get_revision(
    uint64_t /*block_number*/, uint64_t const timestamp) const
{
    auto const monad_revision = get_monad_revision(timestamp);

    if (MONAD_LIKELY(monad_revision >= MONAD_FOUR)) {
        return EVMC_PRAGUE;
    }

    return EVMC_CANCUN;
}

Result<void> MonadChain::validate_output_header(
    BlockHeader const &input, BlockHeader const &output) const
{
    if (MONAD_UNLIKELY(input.ommers_hash != output.ommers_hash)) {
        return BlockError::WrongOmmersHash;
    }
    if (MONAD_UNLIKELY(input.transactions_root != output.transactions_root)) {
        return BlockError::WrongMerkleRoot;
    }
    if (MONAD_UNLIKELY(input.withdrawals_root != output.withdrawals_root)) {
        return BlockError::WrongMerkleRoot;
    }

    // YP eq. 56
    if (MONAD_UNLIKELY(output.gas_used > output.gas_limit)) {
        return BlockError::GasAboveLimit;
    }
    return success();
}

size_t MonadChain::get_max_code_size(
    uint64_t /*block_number*/, uint64_t const timestamp) const
{
    auto const monad_rev = get_monad_revision(timestamp);
    if (MONAD_LIKELY(monad_rev >= MONAD_TWO)) {
        return MAX_CODE_SIZE_MONAD_TWO;
    }
    else if (monad_rev >= MONAD_ZERO) {
        return MAX_CODE_SIZE_EIP170;
    }
    else {
        MONAD_ABORT("invalid revision");
    }
}

size_t MonadChain::get_max_initcode_size(
    uint64_t /*block_number*/, uint64_t const timestamp) const
{
    auto const monad_rev = get_monad_revision(timestamp);

    if (MONAD_LIKELY(monad_rev >= MONAD_FOUR)) {
        return MAX_INITCODE_SIZE_MONAD_FOUR;
    }
    else if (monad_rev >= MONAD_ZERO) {
        return MAX_INITCODE_SIZE_EIP3860;
    }
    else {
        MONAD_ABORT("invalid revision");
    }
}

bool MonadChain::revert_transaction(
    uint64_t const block_number, uint64_t const timestamp,
    Address const &sender, Transaction const &tx,
    uint256_t const &base_fee_per_gas, uint64_t const i, State &state,
    MonadChainContext const &ctx) const
{
    auto const monad_rev = get_monad_revision(timestamp);
    if (MONAD_LIKELY(monad_rev >= MONAD_FOUR)) {
        evmc_revision const rev = get_revision(block_number, timestamp);
        return dipped_into_reserve(
            monad_rev, rev, sender, tx, base_fee_per_gas, i, ctx, state);
    }
    else if (monad_rev >= MONAD_ZERO) {
        return false;
    }
    else {
        MONAD_ABORT("invalid revision for revert");
    }
}

bool can_sender_dip_into_reserve(
    Address const &sender, uint64_t const i, bytes32_t const &orig_code_hash,
    MonadChainContext const &ctx)
{
    if (orig_code_hash != NULL_HASH) { // check delegated
        return false;
    }

    // check pending blocks
    for (ankerl::unordered_dense::segmented_set<Address> const
             *const senders_and_authorities :
         {ctx.grandparent_senders_and_authorities,
          ctx.parent_senders_and_authorities}) {
        if (senders_and_authorities &&
            senders_and_authorities->contains(sender)) {
            return false;
        }
    }

    // check current block
    if (ctx.senders_and_authorities.contains(sender)) {
        for (size_t j = 0; j <= i; ++j) {
            if (j < i && sender == ctx.senders.at(j)) {
                return false;
            }
            if (std::ranges::contains(ctx.authorities.at(j), sender)) {
                return false;
            }
        }
    }

    return true; // Allow dipping into reserve if no restrictions found
}

uint256_t get_max_reserve(monad_revision const rev, Address const &)
{
    // TODO: implement precompile (support reading from orig)
    constexpr uint256_t WEI_PER_MON{1000000000000000000};
    return uint256_t{monad_default_max_reserve_balance_mon(rev)} * WEI_PER_MON;
}

MONAD_NAMESPACE_END
