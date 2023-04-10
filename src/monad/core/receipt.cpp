#include <monad/core/receipt.hpp>

#include <ethash/keccak.hpp>

#include <intx/intx.hpp>

MONAD_NAMESPACE_BEGIN

void set_3_bits(Receipt::Bloom &bloom, byte_string_view const bytes)
{
    auto const h{ethash::keccak256(bytes.cbegin(), bytes.size())};
    for (auto i = 0; i < 3; ++i) {
        // Poorly named intx function, this really is taking from our hash,
        // which is returned as big endian, to host order so we can do calcs on
        // `bit`
        const uint16_t bit =
            intx::to_big_endian(
                reinterpret_cast<uint16_t const *>(h.bytes)[i]) &
            2047u;
        const auto byte = 255u - bit / 8u;
        bloom[byte] |= 1u << (bit & 7u);
    }
}

void populate_bloom(Receipt::Bloom &b, Receipt::Log const &l)
{
    set_3_bits(b, to_byte_string_view(l.address.bytes));
    for (auto const &i : l.topics) {
        set_3_bits(b, to_byte_string_view(i.bytes));
    }
}

void Receipt::add_log(Receipt::Log const &l)
{
    logs.push_back(l);
    populate_bloom(bloom, l);
}

MONAD_NAMESPACE_END
