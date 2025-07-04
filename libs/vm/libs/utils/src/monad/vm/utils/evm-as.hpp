#pragma once

#include <monad/vm/utils/evm-as/builder.hpp>
#include <monad/vm/utils/evm-as/compiler.hpp>
#include <monad/vm/utils/evm-as/instruction.hpp>
#include <monad/vm/utils/evm-as/validator.hpp>

#include <evmc/evmc.h>

namespace monad::vm::utils::evm_as
{

    inline EvmBuilder<EVMC_LATEST_STABLE_REVISION> latest()
    {
        return EvmBuilder<EVMC_LATEST_STABLE_REVISION>{};
    }

    inline EvmBuilder<EVMC_FRONTIER> frontier()
    {
        return EvmBuilder<EVMC_FRONTIER>{};
    }

    inline EvmBuilder<EVMC_HOMESTEAD> homestead()
    {
        return EvmBuilder<EVMC_HOMESTEAD>{};
    }

    inline EvmBuilder<EVMC_TANGERINE_WHISTLE> tangerine_whistle()
    {
        return EvmBuilder<EVMC_TANGERINE_WHISTLE>{};
    }

    inline EvmBuilder<EVMC_SPURIOUS_DRAGON> spurious_dragon()
    {
        return EvmBuilder<EVMC_SPURIOUS_DRAGON>{};
    }

    inline EvmBuilder<EVMC_BYZANTIUM> byzantium()
    {
        return EvmBuilder<EVMC_BYZANTIUM>{};
    }

    inline EvmBuilder<EVMC_CONSTANTINOPLE> constantinople()
    {
        return EvmBuilder<EVMC_CONSTANTINOPLE>{};
    }

    inline EvmBuilder<EVMC_PETERSBURG> petersburg()
    {
        return EvmBuilder<EVMC_PETERSBURG>{};
    }

    inline EvmBuilder<EVMC_ISTANBUL> istanbul()
    {
        return EvmBuilder<EVMC_ISTANBUL>{};
    }

    inline EvmBuilder<EVMC_BERLIN> berlin()
    {
        return EvmBuilder<EVMC_BERLIN>{};
    }

    inline EvmBuilder<EVMC_LONDON> london()
    {
        return EvmBuilder<EVMC_LONDON>{};
    }

    inline EvmBuilder<EVMC_PARIS> paris()
    {
        return EvmBuilder<EVMC_PARIS>{};
    }

    inline EvmBuilder<EVMC_SHANGHAI> shanghai()
    {
        return EvmBuilder<EVMC_SHANGHAI>{};
    }

    inline EvmBuilder<EVMC_CANCUN> cancun()
    {
        return EvmBuilder<EVMC_CANCUN>{};
    }

    inline EvmBuilder<EVMC_PRAGUE> prague()
    {
        return EvmBuilder<EVMC_PRAGUE>{};
    }
}
