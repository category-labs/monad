#include <monad/config.hpp>
#include <monad/core/byte_string.hpp>
#include <monad/core/receipt.hpp>

#include <ethash/keccak.hpp>

#include <intx/intx.hpp>

#include <cstdint>

MONAD_NAMESPACE_BEGIN

void set_3_bits(Receipt::Bloom &bloom, byte_string_view const bytes)
{
    // YP Eqn 29
    auto const h{ethash::keccak256(bytes.cbegin(), bytes.size())};
    for (auto i = 0u; i < 3u; ++i) {
        // Poorly named intx function, this really is taking from our hash,
        // which is returned as big endian, to host order so we can do calcs on
        // `bit`
        uint16_t const bit =
            intx::to_big_endian(
                reinterpret_cast<uint16_t const *>(h.bytes)[i]) &
            2047u;
        unsigned int const byte = 255u - bit / 8u;
        bloom[byte] |= static_cast<unsigned char>(1u << (bit & 7u));
    }
}

void populate_bloom(Receipt::Bloom &bloom, Receipt::Log const &log)
{
    // YP Eqn 28
    set_3_bits(bloom, to_byte_string_view(log.address.bytes));
    for (auto const &i : log.topics) {
        set_3_bits(bloom, to_byte_string_view(i.bytes));
    }
}

void Receipt::add_log(Receipt::Log const &log)
{
    logs.push_back(log);
    populate_bloom(bloom, log);
}

MONAD_NAMESPACE_END
