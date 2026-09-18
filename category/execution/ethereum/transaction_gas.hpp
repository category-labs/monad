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

#include <category/core/checked_math.hpp>
#include <category/core/config.hpp>
#include <category/core/int.hpp>
#include <category/core/result.hpp>
#include <category/execution/ethereum/chain/blob_schedule.hpp>
#include <category/vm/evm/traits.hpp>

#include <evmc/evmc.h>

#include <cstdint>

MONAD_NAMESPACE_BEGIN

struct Transaction;
struct BlockHeader;

// Zero and non-zero calldata byte counts, which EIP-2028 and EIP-7623 price
// differently. Both intrinsic_gas and floor_data_gas need them, and every
// transaction goes through both twice -- once to validate, once to execute --
// so each transaction's calldata was being counted four times. Measured on
// block 25551991: 1,032 counts for 258 transactions, 578,740 steps. The
// counts are a pure function of tx.data, so the caller takes them once and
// hands them down.
struct CalldataTokens
{
    uint64_t zeros;
    uint64_t nonzeros;
};

CalldataTokens tokens_in_calldata(Transaction const &) noexcept;

template <Traits traits>
uint64_t g_data(Transaction const &) noexcept;

template <Traits traits>
uint64_t intrinsic_gas(Transaction const &) noexcept;

// intrinsic_gas for a caller that already holds the counts. A separate name
// rather than an overload: EXPLICIT_TRAITS instantiates through
// `decltype(f<traits>)`, which an overload set makes ambiguous.
template <Traits traits>
uint64_t intrinsic_gas_counted(Transaction const &, CalldataTokens) noexcept;

/// Whether gas is PRICED, as distinct from METERED.
///
/// False on the L2 prototype. The interpreter still counts every opcode, so
/// gas_used stays gas_limit minus what was left and is the gas genuinely
/// consumed -- receipts and the header's gas_used remain verifiable exactly as
/// they are. What goes is the economics: no up-front purchase, no refund
/// credit, no beneficiary payment, no base or priority fee, no blob gas, no
/// calldata floor.
///
/// A predicate read through `if constexpr` rather than #ifdef at each site, for
/// three reasons: the lever is defined once; both branches stay syntactically
/// checked in both configurations, so an L2 build cannot rot the L1 path; and
/// an OFF build is identical because the dead branch is eliminated.
///
/// Not the split-instantiation pattern CLAUDE.md prefers (compute_gas_refund is
/// declared once and defined twice, real for EvmTraits and zero for Monad).
/// That works because the dimension there is a TRAITS VALUE and the linker
/// picks. Here the dimension is the build, so there is nothing to pick between.
inline constexpr bool gas_is_priced() noexcept
{
#if defined(MONAD_ZKVM_L2) && !defined(MONAD_ZKVM_L2_PRICE_GAS)
    return false;
#else
    return true;
#endif
}

// TEMPORARY SCAFFOLD -- MONAD_ZKVM_L2_PRICE_GAS, read above, puts the pricing
// back into an L2 build. It exists for one reason and should be deleted with
// the thing it props up.
//
// A witness is a function of the rules that produced it. The corpus available
// is mainnet, so its state trie is pruned to exactly the accounts and slots
// canonical execution touched; everything else is a Digest node and reading
// one is MONAD_ABORT("incomplete witness"). Unpriced gas changes what
// execution touches -- senders keep their gas money, the beneficiary gets no
// tips -- so the guest walks off the edge of the witness partway through a
// busy block. Measured: block 25815000 aborts mid-execution, before the
// epilogue is reached at all.
//
// Turning pricing back on makes execution follow the rules the witness was
// cut for, which is what lets the corpus differential run at all. What it
// costs is that the arm measured is no longer the arm this branch is about:
// the gas surgery is precisely the L2 semantics being tested. So the
// differential under this knob says something about the CIPHER and nothing
// about the surgery, and the surgery needs a corpus generated under L2 rules
// before it can be exercised end to end.
//
// It would have been a `git revert` of "gas: meter it, stop pricing it", but
// that commit introduces gas_is_priced itself and two later ones read it, so
// a literal revert does not compile. This is the same change expressed where
// it can be switched off again in one line.

/// DIAGNOSTIC ONLY. True when the L2 guest accepts an L1 block shape it has no
/// rules for, so that the corpus differential can run on mainnet witnesses.
/// Off by default, and forbidden in any audited build.
///
/// It exists because the corpus available is Osaka, not the Paris-to-Shanghai
/// window: every block carries withdrawals and a requests_hash, and two thirds
/// carry blob transactions, each of which the L2 refuses outright. With this
/// on, those three are accepted and the parts this chain cannot authenticate
/// are IGNORED rather than implemented -- withdrawals are decoded but never
/// credited, the requests hash is accepted but never recomputed, and a blob
/// transaction executes with no blob fee.
///
/// That makes the executed semantics diverge from mainnet's, which is fine for
/// what it is for and useless for anything else: the differential compares two
/// L2 builds against EACH OTHER, so both arms carry this and it cannot bias
/// the comparison. It creates no balance in either, which is the one property
/// worth keeping even in a build nobody proves: the P1 this lever reaches into
/// stays closed.
inline constexpr bool l2_allows_l1_shape() noexcept
{
#ifdef MONAD_ZKVM_L2_ALLOW_L1_SHAPE
    return true;
#else
    return false;
#endif
}

/// DIAGNOSTIC ONLY. True in the differential's REFERENCE arm: L2 chain, L2 gas
/// rules, L2 block shape and L2 anchor, but a six-field witness whose leaves
/// are plaintext transactions rather than ciphertexts.
///
/// This is what makes the differential an argument about the cipher. Comparing
/// an L2 build against a NON-L2 build compares two different consensus rule
/// sets: gas is priced on one and metered-only on the other, so the sender's
/// balance, the refund and the beneficiary's tips all move on one arm and not
/// the other, and the post-state roots differ on every block that has a
/// transaction. Comparing L2 against L2 leaves the cipher as the only
/// difference, which is the thing being tested.
inline constexpr bool l2_leaves_are_plaintext() noexcept
{
#ifdef MONAD_ZKVM_L2_PLAINTEXT_LEAVES
    return true;
#else
    return false;
#endif
}

uint64_t floor_data_gas(Transaction const &) noexcept;
uint64_t floor_data_gas(CalldataTokens) noexcept;

template <Traits traits>
uint256_t
gas_price(Transaction const &, uint256_t const &base_fee_per_gas) noexcept;

template <Traits traits>
uint64_t g_star(Transaction const &, uint64_t gas_remaining, uint64_t refund);

template <Traits traits>
uint64_t compute_gas_refund(
    Transaction const &, uint64_t gas_remaining, uint64_t refund);

template <Traits traits>
uint256_t calculate_txn_award(
    Transaction const &, uint256_t const &base_fee_per_gas,
    uint64_t gas_used) noexcept;

inline Result<uint256_t>
max_gas_cost(uint64_t const gas_limit, uint256_t const max_fee_per_gas) noexcept
{
    return checked_mul(uint256_t{gas_limit}, max_fee_per_gas);
}

// EIP-4844
inline constexpr uint64_t GAS_PER_BLOB = 131'072;

// EIP-7918
inline constexpr uint64_t BLOB_BASE_COST = 8192;

template <Traits traits>
inline constexpr BlobSchedule default_blob_schedule() noexcept
{
    // EIP-7691 increases the blob count where active.
    if constexpr (traits::eip_7691_active()) {
        return PRAGUE_BLOB_SCHEDULE;
    }
    else {
        return CANCUN_BLOB_SCHEDULE;
    }
}

inline constexpr uint64_t
max_blob_gas_per_block(BlobSchedule const &blob_schedule) noexcept
{
    return blob_schedule.max_blobs_per_block * GAS_PER_BLOB;
}

inline constexpr uint64_t
target_blob_gas_per_block(BlobSchedule const &blob_schedule) noexcept
{
    return blob_schedule.target_blobs_per_block * GAS_PER_BLOB;
}

uint256_t
calc_blob_fee(Transaction const &, uint64_t, BlobSchedule const &) noexcept;

uint256_t get_base_fee_per_blob_gas(uint64_t, BlobSchedule const &) noexcept;

template <Traits traits>
uint64_t calc_excess_blob_gas(
    BlockHeader const &parent_header,
    BlobSchedule const &current_blob_schedule) noexcept;

uint64_t get_total_blob_gas(Transaction const &) noexcept;

MONAD_NAMESPACE_END
