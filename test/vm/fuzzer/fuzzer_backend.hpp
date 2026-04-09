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

#include "fuzzer_view.hpp"

#include <category/core/byte_string.hpp>
#include <category/core/int.hpp>
#include <category/execution/ethereum/core/address.hpp>

#include <evmc/evmc.hpp>

#include <cstddef>
#include <cstdint>
#include <limits>
#include <memory>
#include <span>

namespace monad::vm::fuzzing
{
    using evmc::literals::operator""_address;

    struct GenesisAccount
    {
        Address addr;
        uint256_t balance;
    };

    constexpr auto genesis_address =
        0xBEEFCAFE000000000000000000000000BA5EBA11_address;

    constexpr std::int64_t block_gas_limit = 300'000'000;

    // Genesis account with a large balance, sufficiently small so that
    // token supply will not overflow uint256.
    constexpr auto genesis_account = GenesisAccount{
        .addr = genesis_address,
        .balance = std::numeric_limits<intx::uint256>::max() / 2};

    class FuzzerBackend
    {
    public:
        virtual ~FuzzerBackend() = default;

        // Contract deployment
        virtual Address
        deploy(Address const &from, std::span<uint8_t const> code) = 0;
        Address deploy_delegated(Address const &from, Address const &delegatee);

        // Execution (full transaction semantics handled internally)
        virtual evmc::Result
        execute(evmc_message const &msg, evmc_revision rev) = 0;

        // Checkpoint / rollback
        virtual uint64_t checkpoint() = 0;
        virtual void rollback(uint64_t id) = 0;

        // State query (for message generation)
        virtual byte_string get_code(Address const &) = 0;
        virtual void ensure_exists(Address const &) = 0;

        // State iteration (for comparison)
        virtual void normalize() = 0;
        // The returned view borrows the backend's internal state. It must
        // not outlive any mutation (deploy, execute, rollback, normalize).
        virtual std::unique_ptr<SortedStateView> sorted_view() const = 0;

        // Constants
        virtual size_t max_code_size() const = 0;
    };
}
