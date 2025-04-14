#pragma once

#include <monad/config.hpp>
#include <monad/core/address.hpp>
#include <monad/core/byte_string.hpp>
#include <monad/core/bytes.hpp>
#include <monad/core/int.hpp>

#include <cstdint>
#include <optional>

MONAD_NAMESPACE_BEGIN

inline constexpr Address STAKING_CONTRACT_ADDRESS{0x1000};

struct ValidatorInfo
{
    Address auth_address;
    byte_string_fixed<48> bls_pubkey;
    uint256_t total_stake;
    uint256_t active_stake;
    uint256_t active_shares;
    uint256_t activating_stake;
    uint256_t deactivating_shares;
    uint256_t rewards[2];
};

struct DelegatorInfo
{
    uint256_t active_shares; // shares
    uint256_t deactivating_shares; // shares
    uint256_t activating_stake; // MON
    uint256_t balance;
};

struct WithdrawalRequest
{
    uint256_t validator_id;
    uint256_t shares;
    Address delegator;
};

struct DepositRequest
{
    uint256_t validator_id;
    uint256_t amount;
    Address delegator;
};

MONAD_NAMESPACE_END
