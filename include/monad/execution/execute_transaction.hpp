#pragma once

#include <monad/config.hpp>
#include <monad/core/address.hpp>
#include <monad/core/int.hpp>
#include <monad/core/result.hpp>

#include <evmc/evmc.h>

MONAD_NAMESPACE_BEGIN

class BlockHashBuffer;
struct BlockHeader;
template <evmc_revision>
struct EvmcHost;
struct Receipt;
class State;
struct Transaction;

template <evmc_revision rev>
Receipt execute(
    State &, EvmcHost<rev> &, Transaction const &,
    uint256_t const &base_fee_per_gas, address_t const &beneficiary);

template <evmc_revision rev>
Result<Receipt> validate_and_execute(
    Transaction const &, BlockHeader const &, BlockHashBuffer const &, State &);

MONAD_NAMESPACE_END
