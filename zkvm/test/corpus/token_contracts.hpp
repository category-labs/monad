// Copyright (C) 2026 Category Labs, Inc.
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

// Code, storage layouts and call builders for WrappedToken, PvpSettlement and
// EarnVault. Layouts follow solc --storage-layout; corpus receipt checks
// catch writes to slots the contracts do not read.

#include <category/core/address.hpp>
#include <category/core/byte_string.hpp>
#include <category/core/bytes.hpp>
#include <category/core/config.hpp>
#include <category/core/int.hpp>

#include <cstdint>
#include <vector>

MONAD_NAMESPACE_BEGIN

namespace corpus::tokens
{
    /// Runtime code, decoded once from the checked-in hex.
    byte_string const &wrapped_token_code();
    byte_string const &pvp_settlement_code();
    byte_string const &earn_vault_code();

    /// A storage word: a slot number, or a value as the EVM stores it.
    bytes32_t word(uint256_t const &);
    bytes32_t word(Address const &);

    // ---- WrappedToken ------------------------------------------------------

    /// The top bit of a balance slot: the holder has been admitted. The rest
    /// of the slot is the balance.
    inline constexpr uint256_t ELIGIBLE = uint256_t{1} << 255;

    /// `_balances[holder]`, slot 0.
    bytes32_t balance_slot(Address const &holder);
    /// `allowance[owner][spender]`, slot 1.
    bytes32_t allowance_slot(Address const &owner, Address const &spender);
    inline constexpr uint64_t TOTAL_SUPPLY_SLOT = 2;
    inline constexpr uint64_t ADMIN_SLOT = 3;
    inline constexpr uint64_t SPOKE_SLOT = 4;
    inline constexpr uint64_t L1_BRIDGE_SLOT = 5;

    byte_string transfer(Address const &to, uint256_t const &value);
    byte_string batch_transfer(
        std::vector<Address> const &to, std::vector<uint256_t> const &value);
    byte_string withdraw_to_l1(uint256_t const &value, Address const &l1_to);
    byte_string set_eligible(Address const &holder, bool ok);

    // ---- EarnVault ---------------------------------------------------------

    inline constexpr uint64_t VAULT_ASSET_SLOT = 0;
    /// `verified[owner]`, slot 1.
    bytes32_t vault_verified_slot(Address const &owner);
    /// `sharesOf[owner]`, slot 2.
    bytes32_t vault_shares_slot(Address const &owner);
    inline constexpr uint64_t VAULT_TOTAL_SHARES_SLOT = 3;
    inline constexpr uint64_t VAULT_ADMIN_SLOT = 4;

    byte_string vault_deposit(uint256_t const &assets);
    byte_string vault_withdraw(uint256_t const &assets);

    // ---- PvpSettlement -----------------------------------------------------

    /// PvpSettlement.Payment, field for field.
    struct Payment
    {
        uint256_t ref;
        Address token_a;
        Address debtor;
        Address intermediary;
        uint256_t amount_a;
        Address token_b;
        Address creditor;
        uint256_t amount_b;
    };

    /// keccak256(abi.encode(p)): the key `pending` is written under.
    bytes32_t payment_id(Payment const &);
    /// `pending[id]`, slot 0.
    bytes32_t pvp_pending_slot(bytes32_t const &id);

    byte_string propose(Payment const &);
    byte_string settle(Payment const &);
}

MONAD_NAMESPACE_END
