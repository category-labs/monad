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

#include <category/core/likely.h>
#include <category/execution/ethereum/core/contract/abi_decode.hpp>
#include <category/execution/ethereum/core/contract/abi_signatures.hpp>
#include <category/execution/monad/chain/namespace_chain_id.hpp>
#include <category/execution/monad/namespace_bridge/namespace_bridge_contract.hpp>
#include <category/execution/monad/namespace_bridge/namespace_bridge_error.hpp>
#include <category/vm/evm/explicit_traits.hpp>

#include <boost/outcome/try.hpp>

#include <cstdint>
#include <cstring>

MONAD_ANONYMOUS_NAMESPACE_BEGIN

struct PrecompileSelector
{
    static constexpr uint32_t REGISTER_NAMESPACE =
        abi_encode_selector("registerNamespace(uint64,uint256,address)");
};

static_assert(PrecompileSelector::REGISTER_NAMESPACE == 0x5af98036);

// registerNamespace is the only way to create a namespace; price it 10x
// the staking-contract ballpark to discourage drive-by registrations and
// reflect the long-lived state it adds.
constexpr uint64_t REGISTER_NAMESPACE_COST = 500'000;
constexpr uint64_t FALLBACK_COST = 100;

constexpr size_t ABI_WORD = 32;

monad::Result<uint64_t> decode_namespace_id(
    monad::byte_string_view &input, monad::uint256_t const &network_chain_id)
{
    using namespace monad;
    BOOST_OUTCOME_TRY(auto const chain_id, abi_decode_fixed<u256_be>(input));
    BOOST_OUTCOME_TRY(
        auto maybe_ns,
        namespace_from_chain_id(chain_id.native(), network_chain_id));
    if (!maybe_ns.has_value()) {
        return NamespaceBridgeError::InvalidInput;
    }
    return *maybe_ns;
}

constexpr uint64_t MODE_SELECTOR = 0;
constexpr uint64_t COMMITMENT_SELECTOR = 1;
constexpr uint64_t OWNER_SELECTOR = 2;

MONAD_ANONYMOUS_NAMESPACE_END

MONAD_NAMESPACE_BEGIN

bytes32_t NamespaceBridgeContract::Variables::storage_key(
    uint64_t const ns, uint64_t const selector) noexcept
{
    bytes32_t key{};
    store_be(key.bytes, ns);
    store_be(key.bytes + sizeof(uint64_t), selector);
    return key;
}

StorageVariable<NamespaceMode>
NamespaceBridgeContract::Variables::mode(uint64_t const ns) noexcept
{
    return {
        state_,
        NAMESPACE_BRIDGE_CA,
        storage_key(ns, MODE_SELECTOR)};
}

StorageVariable<bytes32_t>
NamespaceBridgeContract::Variables::commitment(uint64_t const ns) noexcept
{
    return {
        state_,
        NAMESPACE_BRIDGE_CA,
        storage_key(ns, COMMITMENT_SELECTOR)};
}

StorageVariable<Address>
NamespaceBridgeContract::Variables::owner(uint64_t const ns) noexcept
{
    return {
        state_,
        NAMESPACE_BRIDGE_CA,
        storage_key(ns, OWNER_SELECTOR)};
}

NamespaceBridgeContract::NamespaceBridgeContract(
    State &state, CallTracerBase &call_tracer,
    uint256_t const &network_chain_id)
    : state_{state}
    , call_tracer_{call_tracer}
    , network_chain_id_{network_chain_id}
    , vars{state}
{
}

template <Traits traits>
std::pair<NamespaceBridgeContract::PrecompileFunc, uint64_t>
NamespaceBridgeContract::precompile_dispatch(byte_string_view &input)
{
    if (MONAD_UNLIKELY(input.size() < 4)) {
        return {&NamespaceBridgeContract::precompile_fallback, FALLBACK_COST};
    }

    auto const signature = load_be_unsafe<uint32_t>(input.substr(0, 4).data());
    input.remove_prefix(4);

    switch (signature) {
    case PrecompileSelector::REGISTER_NAMESPACE:
        return {
            &NamespaceBridgeContract::precompile_register_namespace,
            REGISTER_NAMESPACE_COST};
    default:
        return {&NamespaceBridgeContract::precompile_fallback, FALLBACK_COST};
    }
}

EXPLICIT_MONAD_TRAITS_MEMBER(NamespaceBridgeContract::precompile_dispatch);

Result<byte_string> NamespaceBridgeContract::precompile_register_namespace(
    byte_string_view input, Address const &, uint256_be_t const &msg_value)
{
    // Registration is initiated from the global namespace.
    if (state_.get_namespace().has_value()) {
        return NamespaceBridgeError::WrongContext;
    }
    if (input.size() != 3 * ABI_WORD) {
        return NamespaceBridgeError::InvalidInput;
    }
    // Not payable.
    uint256_t const value = load_be<uint256_t>(msg_value);
    if (value != 0) {
        return NamespaceBridgeError::InvalidAmount;
    }

    BOOST_OUTCOME_TRY(auto ns, decode_namespace_id(input, network_chain_id_));
    BOOST_OUTCOME_TRY(auto const mode, abi_decode_fixed<u256_be>(input));
    if (mode.native() != static_cast<uint8_t>(NamespaceMode::Native)) {
        return NamespaceBridgeError::InvalidInput;
    }
    BOOST_OUTCOME_TRY(auto const owner, abi_decode_fixed<Address>(input));

    if (vars.mode(ns).load() != NamespaceMode::None) {
        return NamespaceBridgeError::NamespaceAlreadyRegistered;
    }

    if (state_.account_is_dead(NAMESPACE_BRIDGE_CA)) {
        state_.set_nonce(NAMESPACE_BRIDGE_CA, 1);
    }
    vars.mode(ns).store(NamespaceMode::Native);
    vars.commitment(ns).store(NULL_ROOT);
    vars.owner(ns).store(owner);

    return byte_string{};
}

Result<byte_string> NamespaceBridgeContract::precompile_fallback(
    byte_string_view, Address const &, uint256_be_t const &)
{
    return NamespaceBridgeError::MethodNotSupported;
}

MONAD_NAMESPACE_END
