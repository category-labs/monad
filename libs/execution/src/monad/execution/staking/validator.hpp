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
    Address withdrawal_address;
    byte_string_fixed<48> bls_pubkey;
    uint256_t stake;
    uint256_t active_stake;
    uint64_t join_epoch;

    bool in_valset(uint64_t const epoch) const noexcept
    {
        return epoch - join_epoch >= 2;
    }

    bool is_leaving_valset() const noexcept
    {
        return stake == 0;
    }
};

struct StakeMetadata
{
    uint64_t withdrawal_queue_size;
    uint64_t deposit_queue_size;
    uint64_t validator_set_size;
};

static_assert(sizeof(StakeMetadata) == 24);
static_assert(alignof(StakeMetadata) == 8);

MONAD_NAMESPACE_END
