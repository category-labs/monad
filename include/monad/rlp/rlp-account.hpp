#pragma once

#include "evmc/evmc.hpp"
#include <monad/config.hpp>
#include <monad/core/account.hpp>
#include <monad/rlp/rlp.hpp>

MONAD_NAMESPACE_BEGIN

namespace rlp
{
    namespace account
    {
        Encoding encode(Account const &a, evmc::bytes32 const &code_root)
        {
            return rlp::encode(a.nonce, a.balance, code_root, a.code_hash);
        }
    }

}
MONAD_NAMESPACE_END
