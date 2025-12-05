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

#include <category/core/assert.h>
#include <category/core/config.hpp>
#include <category/core/monad_exception.hpp>
#include <category/execution/ethereum/core/transaction.hpp>
#include <category/execution/ethereum/state3/state.hpp>
#include <category/execution/ethereum/transaction_gas.hpp>
#include <category/execution/monad/chain/monad_chain.hpp>
#include <category/execution/monad/reserve_balance.h>
#include <category/execution/monad/reserve_balance.hpp>
#include <category/vm/evm/delegation.hpp>
#include <category/vm/evm/monad/revision.h>
#include <category/vm/interpreter/intercode.hpp>

#include <ankerl/unordered_dense.h>

#include <algorithm>
#include <cstddef>
#include <optional>
#include <ranges>

unsigned monad_default_max_reserve_balance_mon(enum monad_revision)
{
    return 10;
}

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
    for (auto const &[addr, cur_account] : state.current()) {
        MONAD_ASSERT(orig.contains(addr));
        bytes32_t const orig_code_hash = orig.at(addr).get_code_hash();
        bytes32_t const effective_code_hash =
            (monad_rev >= MONAD_EIGHT) ? cur_account.recent().get_code_hash()
                                       : orig_code_hash;
        bool effective_is_delegated = false;

        // Skip if not EOA
        if (effective_code_hash != NULL_HASH) {
            vm::SharedIntercode const intercode =
                state.read_code(effective_code_hash)->intercode();
            effective_is_delegated = monad::vm::evm::is_delegated(
                {intercode->code(), intercode->size()});
            if (!effective_is_delegated) {
                continue;
            }
        }

        // Check if dipped into reserve
        std::optional<uint256_t> const violation_threshold =
            [&] -> std::optional<uint256_t> {
            uint256_t const orig_balance = intx::be::load<uint256_t>(
                state.get_original_balance_pessimistic(addr));
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
        uint256_t const curr_balance = intx::be::load<uint256_t>(
            state.get_current_balance_pessimistic(addr));
        if (!violation_threshold.has_value() ||
            curr_balance < violation_threshold.value()) {
            if (addr == sender) {
                if (!can_sender_dip_into_reserve(
                        sender, i, effective_is_delegated, ctx)) {
                    // Safety: this assertion is recoverable because it can be
                    // triggered via RPC parameter setting.
                    MONAD_ASSERT_THROW(
                        violation_threshold.has_value(),
                        "gas fee greater than reserve for non-dipping "
                        "transaction");
                    return true;
                }
                // Skip if allowed to dip into reserve
            }
            else {
                // Safety: this assertion should not be a recoverable one, as it
                // indicates a logic error in the surrounding code: the
                // violation threshold can only be nullopt when addr == sender,
                // which is not the case in this branch.
                MONAD_ASSERT(violation_threshold.has_value());
                return true;
            }
        }
    }
    return false;
}

MONAD_ANONYMOUS_NAMESPACE_END

MONAD_NAMESPACE_BEGIN

bool revert_monad_transaction(
    monad_revision const monad_rev, evmc_revision const rev,
    Address const &sender, Transaction const &tx,
    uint256_t const &base_fee_per_gas, uint64_t const i, State &state,
    MonadChainContext const &ctx)
{
    if (MONAD_LIKELY(monad_rev >= MONAD_FOUR)) {
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
    Address const &sender, uint64_t const i, bool const sender_is_delegated,
    MonadChainContext const &ctx)
{
    if (sender_is_delegated) { // delegated accounts cannot dip
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
