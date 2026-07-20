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

#include <category/core/address.hpp>
#include <category/core/byte_string.hpp>
#include <category/core/config.hpp>
#include <category/core/int.hpp>
#include <category/core/result.hpp>
#include <category/execution/ethereum/core/contract/storage_variable.hpp>
#include <category/execution/ethereum/state3/state.hpp>
#include <category/execution/ethereum/trace/call_tracer.hpp>
#include <category/vm/evm/traits.hpp>

#include <optional>

MONAD_NAMESPACE_BEGIN

// Namespace bridge precompile.
inline constexpr Address NAMESPACE_BRIDGE_CA = Address{0x1002};

enum class NamespaceMode : uint8_t
{
    None = 0,
    Native = 1
};

class NamespaceBridgeContract
{
    State &state_;
    [[maybe_unused]] CallTracerBase &call_tracer_;
    // Current tx chain_id, used as the network chain_id when validating the
    // namespace-qualified chain_id supplied to registerNamespace.
    uint256_t network_chain_id_;

public:
    //////////////////////////////
    // Bridge Storage Variables //
    //////////////////////////////
    class Variables
    {
        State &state_;
        static bytes32_t storage_key(uint64_t, uint64_t selector) noexcept;

    public:
        explicit Variables(State &state)
            : state_{state}
        {
        }

        StorageVariable<NamespaceMode> mode(uint64_t ns) noexcept;
        StorageVariable<bytes32_t> commitment(uint64_t ns) noexcept;
        StorageVariable<Address> owner(uint64_t ns) noexcept;
    } vars;

    NamespaceBridgeContract(
        State &state, CallTracerBase &, uint256_t const &network_chain_id);

    using PrecompileFunc = Result<byte_string> (NamespaceBridgeContract::*)(
        byte_string_view, Address const &, uint256_be_t const &);

    template <Traits traits>
    static std::pair<PrecompileFunc, uint64_t>
    precompile_dispatch(byte_string_view &);

    // registerNamespace(uint64 chain_id, uint256 mode, address owner)
    // Global-scope, non-payable native namespace registration. Writes the
    // immutable mode and owner slots; tx revert discards the storage change.
    // owner == address(0) leaves the namespace permissionless.
    Result<byte_string> precompile_register_namespace(
        byte_string_view, Address const &, uint256_be_t const &);

    Result<byte_string> precompile_fallback(
        byte_string_view, Address const &, uint256_be_t const &);
};

MONAD_NAMESPACE_END
