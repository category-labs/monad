#include <monad/core/signature.hpp>

MONAD_NAMESPACE_BEGIN

void SignatureAndChain::from_v(uint64_t const &v)
{
    if (v == 28) {
        odd_y_parity = true;
    }
    else if (v == 27) {
        odd_y_parity = false;
    }
    else // chain_id has value
    {
        auto tmp = v - 35;
        if (tmp & 1) {
            odd_y_parity = true;
            tmp ^= 1;
        }
        chain_id = tmp >> 1;
    }
}

uint64_t get_v(SignatureAndChain const &sc) noexcept
{
    if (sc.chain_id.has_value()) {
        return (*sc.chain_id * 2) + 35 + (int)sc.odd_y_parity;
    }
    return sc.odd_y_parity ? 28 : 27;
}

MONAD_NAMESPACE_END
