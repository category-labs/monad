#pragma once

#include <monad/config.hpp>

#include <monad/core/address.hpp>
#include <monad/core/bytes.hpp>

#include <ethash/hash_types.hpp>

MONAD_NAMESPACE_BEGIN

Address create_contract_address(Address const &from, uint64_t const nonce);
Address create2_contract_address(
    Address const &from, bytes32_t const &zeta,
    ethash::hash256 const &code_hash);

MONAD_NAMESPACE_END
