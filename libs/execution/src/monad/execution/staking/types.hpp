#pragma once

#include <monad/config.hpp>
#include <monad/contract/uint256.hpp>
#include <monad/core/address.hpp>
#include <monad/core/byte_string.hpp>
#include <monad/core/bytes.hpp>

#include <cstdint>
#include <memory>
#include <optional>
#include <span>

#include <intx/intx.hpp>

MONAD_NAMESPACE_BEGIN

using namespace intx::literals;

inline constexpr Address STAKING_CONTRACT_ADDRESS{0x1000};
inline constexpr auto MIN_STAKE_AMOUNT = 1000000000000000000_u256;
inline constexpr auto BASE_STAKING_REWARD = 1000000000000000000_u256;

#pragma pack(push, 1)

struct ValidatorInfo
{
    Address auth_address;
    byte_string_fixed<48> bls_pubkey;
    Uint256BE active_stake;
    Uint256BE active_shares;
    Uint256BE rewards[2];
};

static_assert(sizeof(ValidatorInfo) == 196);
static_assert(alignof(ValidatorInfo) == 1);

struct DelegatorInfo
{
    Uint256BE active_shares; // shares
    Uint256BE balance;
};

static_assert(sizeof(DelegatorInfo) == 64);
static_assert(alignof(DelegatorInfo) == 1);

struct WithdrawalRequest
{
    Uint256BE validator_id;
    Address delegator;
    Uint256BE shares;
};

static_assert(sizeof(WithdrawalRequest) == 84);
static_assert(alignof(WithdrawalRequest) == 1);

struct DepositRequest
{
    Uint256BE validator_id;
    Address delegator;
    Uint256BE amount;
};

static_assert(sizeof(DepositRequest) == 84);
static_assert(alignof(DepositRequest) == 1);

#pragma pack(pop)

std::span<uint8_t> abi_encode_validator_info(ValidatorInfo const &);
std::span<uint8_t> abi_encode_delegator_info(DelegatorInfo const &);
std::span<uint8_t> abi_encode_deposit_request(DepositRequest const &);
std::span<uint8_t> abi_encode_withdrawal_request(WithdrawalRequest const &);

MONAD_NAMESPACE_END
