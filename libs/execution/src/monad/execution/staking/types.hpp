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
    Uint256BE rewards;
};

static_assert(sizeof(ValidatorInfo) == 164);
static_assert(alignof(ValidatorInfo) == 1);

struct DelegatorInfo
{
    Uint256BE active_shares; // shares
    Uint256BE balance;
};

static_assert(sizeof(DelegatorInfo) == 64);
static_assert(alignof(DelegatorInfo) == 1);

struct UndelegateRequest
{
    Uint256BE validator_id;
    Address delegator;
    Uint256BE shares;
};

static_assert(sizeof(UndelegateRequest) == 84);
static_assert(alignof(UndelegateRequest) == 1);

struct DelegateRequest
{
    Uint256BE validator_id;
    Address delegator;
    Uint256BE amount;
};

static_assert(sizeof(DelegateRequest) == 84);
static_assert(alignof(DelegateRequest) == 1);

struct WithdrawalRequest
{
    Uint256BE validator_id;
    Address delegator;
    Uint256BE pending_balance;
};

static_assert(sizeof(WithdrawalRequest) == 84);
static_assert(alignof(WithdrawalRequest) == 1);

#pragma pack(pop)

std::span<uint8_t> abi_encode_validator_info(ValidatorInfo const &);
std::span<uint8_t> abi_encode_delegator_info(DelegatorInfo const &);
std::span<uint8_t> abi_encode_delegate_request(DelegateRequest const &);
std::span<uint8_t> abi_encode_undelegate_request(UndelegateRequest const &);

MONAD_NAMESPACE_END
