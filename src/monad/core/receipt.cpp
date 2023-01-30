#include <ethash/keccak.hpp>
#include <monad/core/receipt.hpp>

#include <endian.h>

MONAD_NAMESPACE_BEGIN

void set_3_bits(Receipt::Bloom &bloom, byte_string_view const bytes)
{
    auto const h{ethash::keccak256(bytes.cbegin(), bytes.size())};
    for (auto i = 0; i < 3; ++i) {
        const uint16_t bit =
            be16toh(reinterpret_cast<uint16_t const *>(h.bytes)[i]) & 2047;
        const auto byte = 255 - bit / 8;
        bloom[byte] |= 1 << (bit & 7);
    }
}

void populate_bloom(Receipt::Bloom &b, Receipt::Log const &l)
{
    set_3_bits(b, byte_string_view{l.address.bytes, sizeof(l.address.bytes)});
    for (auto const &i : l.topics) {
        set_3_bits(b, byte_string_view{i.bytes, sizeof(bytes32_t)});
    }
}

void Receipt::add_log(Receipt::Log const &l)
{
    logs.push_back(l);
    populate_bloom(bloom, l);
}

MONAD_NAMESPACE_END
