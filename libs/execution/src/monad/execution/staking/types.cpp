#include <monad/core/assert.h>
#include <monad/execution/staking/types.hpp>

#include <cstdlib>
#include <intx/intx.hpp>

MONAD_NAMESPACE_BEGIN

std::span<uint8_t> abi_encode_validator_info(ValidatorInfo const &v)
{
    auto *ptr = static_cast<uint8_t *>(malloc(224));
    MONAD_ASSERT(ptr);

    // auth address
    std::memset(ptr, 0, 12);
    std::memcpy(ptr + 12, v.auth_address.bytes, 20);
    ptr += 32;

    // bls pubkey
    std::memcpy(ptr, v.bls_pubkey.data(), 48);
    std::memset(ptr + 48, 0, 16);
    ptr += 64;

    // remaining fields are be encoded uint256
    std::memcpy(ptr, &v.active_shares, 128);
    return {ptr, 224};
}

MONAD_NAMESPACE_END
