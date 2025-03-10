#include <monad/core/address.hpp>
#include <monad/core/assert.h>
#include <monad/core/keccak.hpp>

#include <algorithm>

MONAD_NAMESPACE_BEGIN

Address address_from_secpkey(byte_string_fixed<65> const &serialized_pubkey)
{
    Address eth_address{};
    MONAD_ASSERT(serialized_pubkey[0] == 4);
    auto const hash = keccak256(serialized_pubkey.data() + 1);
    std::copy_n(hash.bytes + 12, sizeof(Address), eth_address.bytes);
    return eth_address;
}

MONAD_NAMESPACE_END
