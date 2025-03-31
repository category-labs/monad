#pragma once

#include <monad/config.hpp>
#include <monad/core/address.hpp>
#include <monad/core/byte_string.hpp>
#include <monad/core/bytes.hpp>
#include <monad/core/int.hpp>

#include <cstdint>
#include <optional>

MONAD_NAMESPACE_BEGIN

struct ValidatorInfo
{
    Address auth_address;
    byte_string_fixed<48> bls_pubkey;
    uint256_t total_stake;
    uint256_t active_stake;
    uint256_t activating_stake;
    uint256_t deactivating_stake;
    uint256_t epoch_rewards;
};

struct DelegatorInfo
{
    uint256_t shares;
    uint256_t balance;
};

struct StakeDelta
{
    uint256_t validator_id;
    uint256_t amount;
    Address delegator;
    bool is_deposit;
};

MONAD_NAMESPACE_END
