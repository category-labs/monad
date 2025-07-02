#include <monad/config.hpp>
#include <monad/core/int.hpp>
#include <monad/core/signature.hpp>

MONAD_NAMESPACE_BEGIN

void SignatureAndChain::from_v(uint256_t const &v)
{
    if (v == 28u) {
        y_parity = 1;
    }
    else if (v == 27u) {
        y_parity = 0;
    }
    else // chain_id has value
    {
        auto tmp = v - 35;
        if (tmp & 1u) {
            y_parity = 1;
            tmp ^= 1u;
        }
        chain_id = tmp >> 1;
    }
}

uint256_t get_v(SignatureAndChain const &sc) noexcept
{
    if (sc.chain_id.has_value()) {
        return (*sc.chain_id * 2u) + 35u + sc.y_parity;
    }
    return sc.y_parity ? 28u : 27u;
}

MONAD_NAMESPACE_END
