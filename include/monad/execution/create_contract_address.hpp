#pragma once

#include <monad/config.hpp>

#include <monad/core/address.hpp>
#include <monad/core/bytes.hpp>

#include <ethash/hash_types.hpp>

MONAD_NAMESPACE_BEGIN

address_t create_contract_address(address_t const &from, uint64_t const nonce);
address_t create2_contract_address(
    address_t const &from, bytes32_t const &zeta,
    ethash::hash256 const &code_hash);

MONAD_NAMESPACE_END
