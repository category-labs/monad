#include <monad/core/address.hpp>

#include <monad/execution/config.hpp>

#include <monad/rlp/encode_helpers.hpp>

#include <ethash/keccak.hpp>

#include <cstring>

MONAD_EXECUTION_NAMESPACE_BEGIN

// YP Sec 7: Eq 85 and 86
address_t hash_and_clip(byte_string const &b)
{
    auto const h = ethash::keccak256(b.data(), b.size());
    address_t result{};
    std::memcpy(result.bytes, &(h.bytes[12]), sizeof(address_t));
    return result;
}

// YP Sec 7: Eq 87, top
address_t create_contract_address(address_t const &from, uint64_t const nonce)
{
    byte_string b = rlp::encode_list(
        rlp::encode_address(from) + rlp::encode_unsigned(nonce));
    return hash_and_clip(b);
}

// EIP-1014 YP Sec 7: Eq 87, bottom
address_t create2_contract_address(
    address_t const &from, bytes32_t const &zeta,
    ethash::hash256 const &code_hash)
{
    byte_string b = byte_string{0xff} +
                    byte_string{from.bytes, sizeof(address_t)} +
                    byte_string{zeta.bytes, sizeof(bytes32_t)} +
                    byte_string{code_hash.bytes, sizeof(ethash::hash256)};
    return hash_and_clip(b);
}

MONAD_EXECUTION_NAMESPACE_END
