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

MONAD_NAMESPACE_END
