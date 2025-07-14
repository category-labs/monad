#include <category/core/byte_string.hpp>
#include <category/core/bytes.hpp>
#include <category/core/config.hpp>
#include <category/core/keccak.hpp>
#include <monad/core/address.hpp>
#include <monad/core/rlp/address_rlp.hpp>
#include <monad/core/rlp/int_rlp.hpp>
#include <monad/rlp/encode2.hpp>

#include <ethash/hash_types.hpp>

#include <cstdint>
#include <cstring>

MONAD_NAMESPACE_BEGIN

// YP Sec 7: Eq 85 and 86
Address hash_and_clip(byte_string const &b)
{
    auto const h = keccak256(b);
    Address result{};
    std::memcpy(result.bytes, &h.bytes[12], sizeof(Address));
    return result;
}

// YP Sec 7: Eq 87, top
Address create_contract_address(Address const &from, uint64_t const nonce)
{
    byte_string const b = rlp::encode_list2(
        rlp::encode_address(from) + rlp::encode_unsigned(nonce));
    return hash_and_clip(b);
}

// EIP-1014 YP Sec 7: Eq 87, bottom
Address create2_contract_address(
    Address const &from, bytes32_t const &zeta,
    ethash::hash256 const &code_hash)
{
    byte_string const b = byte_string{0xff} +
                          byte_string{from.bytes, sizeof(Address)} +
                          byte_string{zeta.bytes, sizeof(bytes32_t)} +
                          byte_string{code_hash.bytes, sizeof(ethash::hash256)};
    return hash_and_clip(b);
}

MONAD_NAMESPACE_END
