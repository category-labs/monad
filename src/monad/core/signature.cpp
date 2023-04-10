#include <monad/core/signature.hpp>

MONAD_NAMESPACE_BEGIN

void SignatureAndChain::from_v(uint64_t const &v)
{
    if (v == 28u) {
        odd_y_parity = true;
    }
    else if (v == 27u) {
        odd_y_parity = false;
    }
    else // chain_id has value
    {
        auto tmp = v - 35;
        if (tmp & 1u) {
            odd_y_parity = true;
            tmp ^= 1u;
        }
        chain_id = tmp >> 1;
    }
}

uint64_t get_v(SignatureAndChain const &sc) noexcept
{
    if (sc.chain_id.has_value()) {
        return (*sc.chain_id * 2u) + 35u + sc.odd_y_parity;
    }
    return sc.odd_y_parity ? 28u : 27u;
}

MONAD_NAMESPACE_END
