#include <monad/core/assert.h>
#include <monad/execution/staking/types.hpp>

#include <cstdlib>
#include <intx/intx.hpp>

MONAD_NAMESPACE_BEGIN

std::span<uint8_t> abi_encode_validator_info(ValidatorInfo const &v)
{
    auto *const ptr = static_cast<uint8_t *>(malloc(224));
    MONAD_ASSERT(ptr);

    auto *q = ptr;

    // auth address
    std::memset(q, 0, 12);
    std::memcpy(q + 12, v.auth_address.bytes, 20);
    q += 32;

    // bls pubkey
    std::memcpy(q, v.bls_pubkey.data(), 48);
    std::memset(q + 48, 0, 16);
    q += 64;

    // remaining fields are be encoded uint256
    std::memcpy(q, &v.active_shares, 128);
    return {ptr, 224};
}

std::span<uint8_t> abi_encode_delegator_info(DelegatorInfo const &d)
{
    auto *const ptr = static_cast<uint8_t *>(malloc(64));
    MONAD_ASSERT(ptr);

    std::memcpy(ptr, &d, sizeof(DelegatorInfo));
    return {ptr, 64};
}

std::span<uint8_t> abi_encode_deposit_request(DepositRequest const &r)
{
    auto *const ptr = static_cast<uint8_t *>(malloc(96));
    MONAD_ASSERT(ptr);

    auto *q = ptr;

    std::memcpy(q, r.validator_id.raw.bytes, 32);
    std::memset(q, 0, 12);
    std::memcpy(q + 12, r.delegator.bytes, 20);
    std::memcpy(q, r.amount.raw.bytes, 32);

    return {ptr, 96};
}

std::span<uint8_t> abi_encode_withdrawal_request(WithdrawalRequest const &r)
{
    auto *const ptr = static_cast<uint8_t *>(malloc(96));
    MONAD_ASSERT(ptr);

    auto *q = ptr;

    std::memcpy(q, r.validator_id.raw.bytes, 32);
    std::memset(q, 0, 12);
    std::memcpy(q + 12, r.delegator.bytes, 20);
    std::memcpy(q, r.shares.raw.bytes, 32);

    return {ptr, 96};
}

MONAD_NAMESPACE_END
