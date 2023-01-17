#include <monad/core/signature.hpp>

MONAD_NAMESPACE_BEGIN

uint64_t get_v(SignatureAndChain const &sc) noexcept
{
    if (sc.chain_id.has_value()) {
        return (*sc.chain_id * 2) + 35 + (int)sc.odd_y_parity;
    }
    return sc.odd_y_parity ? 28 : 27;
}

MONAD_NAMESPACE_END
