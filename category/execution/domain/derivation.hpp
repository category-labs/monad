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
#include <category/core/bytes.hpp>
#include <category/core/result.hpp>
#include <category/execution/domain/config.hpp>
#include <category/execution/domain/inputs.hpp>
#include <category/execution/ethereum/core/transaction.hpp>

#include <cstdint>
#include <functional>
#include <initializer_list>
#include <optional>
#include <vector>

// TODO unstable paths between versions
#if __has_include(<boost/outcome/experimental/status-code/status-code/config.hpp>)
    #include <boost/outcome/experimental/status-code/status-code/config.hpp>
    #include <boost/outcome/experimental/status-code/status-code/quick_status_code_from_enum.hpp>
#else
    #include <boost/outcome/experimental/status-code/config.hpp>
    #include <boost/outcome/experimental/status-code/quick_status_code_from_enum.hpp>
#endif

MONAD_DOMAIN_NAMESPACE_BEGIN

// Price of one unit of domain gas in L1 wei, and the most gas the hub sells
// per domain per L1 block. Mirror DomainHub.DOMAIN_GAS_PRICE and
// DomainHub.DOMAIN_BLOCK_GAS_LIMIT. Every domain block has this gas limit and
// this base fee.
inline constexpr uint256_t DOMAIN_GAS_PRICE{50'000'000'000};
inline constexpr uint64_t DOMAIN_BLOCK_GAS_LIMIT = 150'000'000;

// Domain gas a fee paid to the hub buys.
uint64_t purchased_domain_gas(uint256_t const &fee);

// The domain being derived: its chain id, which its transactions carry, and
// its spoke, which its deliveries call.
struct DomainConfig
{
    uint64_t chain_id{};
    Address spoke{};
};

enum class DomainDerivationError
{
    Success = 0,
    // The domain has inputs, but its registration was never derived:
    // derivation started after it.
    NotRegistered,
    // The domain is registered again. The hub registers a domain once.
    AlreadyRegistered,
    // The domain has executed blocks the hub has not recorded: its db and
    // the L1 are not of the same chain.
    AheadOfHub,
};

// A domain block as derivation hands it to execution: the values it executes
// under, its transactions and their senders. Executing the blocks from
// genesis in order rebuilds the domain's state. A block has no encoding and
// no id: it is handed on in memory, never stored or sent.
struct DerivedDomainBlock
{
    // Domain block height: 0 is genesis, then +1 per derived block. Not the
    // L1 block number.
    uint64_t number{};
    // The L1 block the domain block is derived from.
    uint64_t l1_block_number{};
    // Copied from the L1 block. slot_number (EIP-7843) is present iff its
    // header has it.
    uint64_t timestamp{};
    bytes32_t prev_randao{};
    std::optional<uint64_t> slot_number{};
    std::vector<Transaction> transactions{};
    // Sender of each transaction: recovered for sequenced transactions,
    // DOMAIN_SYSTEM_RELAYER for message deliveries.
    std::vector<Address> senders{};

    friend bool operator==(
        DerivedDomainBlock const &, DerivedDomainBlock const &) = default;
};

// Opens one sequenced transaction sealed to the domain's key; see
// PrivateDomainKey::open_transaction.
using DomainTransactionOpener =
    std::function<Result<byte_string>(byte_string_view payload)>;

// Derives at most one block of a domain from its inputs in one L1 block,
// following PROTOCOL.md in category-labs/monad-domains. `next_block` is the
// number the domain's next block gets: none until its registration is
// derived.
//   - The domain gets a block iff the L1 block registers it (genesis, block
//     0) or holds at least one input, whether or not any input survives the
//     derivation rules.
//   - The block holds the sequenced transactions that survive, in L1 order,
//     then one delivery per plaintext L1 message, in hub nonce order.
//     Encrypted messages are not delivered.
// Reads no domain state. Fails if the registration does not come first and
// once.
Result<std::optional<DerivedDomainBlock>> derive_domain_block(
    DomainInputs const &, DomainConfig const &,
    std::optional<uint64_t> next_block, DomainTransactionOpener const &);

MONAD_DOMAIN_NAMESPACE_END

BOOST_OUTCOME_SYSTEM_ERROR2_NAMESPACE_BEGIN

template <>
struct quick_status_code_from_enum<monad::domain::DomainDerivationError>
    : quick_status_code_from_enum_defaults<monad::domain::DomainDerivationError>
{
    static constexpr auto const domain_name = "Domain Derivation Error";
    static constexpr auto const domain_uuid =
        "7d0c5f0e-2a53-4f2b-9d0e-6c1b6f4a9e35";

    static std::initializer_list<mapping> const &value_mappings();
};

BOOST_OUTCOME_SYSTEM_ERROR2_NAMESPACE_END
