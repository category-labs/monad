#pragma once

#include <monad/evm/config.hpp>

MONAD_EVM_NAMESPACE_BEGIN

enum Revision
{
    Frontier = 0,
    Homestead = 1,
    TangerineWhistle = 2,
    SpuriousDragon = 3,
    Byzantium = 4,
    Constantinople = 5,
    Petersburg = 6,
    Istanbul = 7,
    Berlin = 8,
    London = 9,
    Paris = 10,
    Shanghai = 11,
};

MONAD_EVM_NAMESPACE_END
