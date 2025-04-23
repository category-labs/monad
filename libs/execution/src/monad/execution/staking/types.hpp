#pragma once

#include <monad/config.hpp>
#include <monad/contract/uint256.hpp>
#include <monad/core/address.hpp>
#include <monad/core/byte_string.hpp>
#include <monad/core/bytes.hpp>

#include <cstdint>
#include <optional>

#include <intx/intx.hpp>

MONAD_NAMESPACE_BEGIN

using namespace intx::literals;

inline constexpr Address STAKING_CONTRACT_ADDRESS{0x1000};
inline constexpr auto MIN_STAKE_AMOUNT = 1000000000000000000_u256;
inline constexpr auto BASE_STAKING_REWARD = 1000000000000000000_u256;

struct ValidatorInfo
{
    Address auth_address;
    byte_string_fixed<48> bls_pubkey;
    Uint256BE total_stake;
    Uint256BE active_stake;
    Uint256BE active_shares;
    Uint256BE activating_stake;
    Uint256BE deactivating_shares;
    Uint256BE rewards[2];
};

struct DelegatorInfo
{
    Uint256BE active_shares; // shares
    Uint256BE deactivating_shares; // shares
    Uint256BE activating_stake; // MON
    Uint256BE balance;
};

struct WithdrawalRequest
{
    Uint256BE validator_id;
    Address delegator;
    Uint256BE shares;
};

struct DepositRequest
{
    Uint256BE validator_id;
    Address delegator;
    Uint256BE amount;
};

MONAD_NAMESPACE_END
