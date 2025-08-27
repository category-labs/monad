// Copyright (C) 2025 Category Labs, Inc.
//
// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with this program.  If not, see <http://www.gnu.org/licenses/>.

#pragma once

#include <category/vm/evm/chain.hpp>
#include <category/vm/utils/evm-as/builder.hpp>
#include <category/vm/utils/evm-as/compiler.hpp>
#include <category/vm/utils/evm-as/instruction.hpp>
#include <category/vm/utils/evm-as/validator.hpp>

#include <evmc/evmc.h>

namespace monad::vm::utils::evm_as
{

    inline EvmBuilder<EvmChain<EVMC_LATEST_STABLE_REVISION>> latest()
    {
        return EvmBuilder<EvmChain<EVMC_LATEST_STABLE_REVISION>>{};
    }

    inline EvmBuilder<EvmChain<EVMC_FRONTIER>> frontier()
    {
        return EvmBuilder<EvmChain<EVMC_FRONTIER>>{};
    }

    inline EvmBuilder<EvmChain<EVMC_HOMESTEAD>> homestead()
    {
        return EvmBuilder<EvmChain<EVMC_HOMESTEAD>>{};
    }

    inline EvmBuilder<EvmChain<EVMC_TANGERINE_WHISTLE>> tangerine_whistle()
    {
        return EvmBuilder<EvmChain<EVMC_TANGERINE_WHISTLE>>{};
    }

    inline EvmBuilder<EvmChain<EVMC_SPURIOUS_DRAGON>> spurious_dragon()
    {
        return EvmBuilder<EvmChain<EVMC_SPURIOUS_DRAGON>>{};
    }

    inline EvmBuilder<EvmChain<EVMC_BYZANTIUM>> byzantium()
    {
        return EvmBuilder<EvmChain<EVMC_BYZANTIUM>>{};
    }

    inline EvmBuilder<EvmChain<EVMC_CONSTANTINOPLE>> constantinople()
    {
        return EvmBuilder<EvmChain<EVMC_CONSTANTINOPLE>>{};
    }

    inline EvmBuilder<EvmChain<EVMC_PETERSBURG>> petersburg()
    {
        return EvmBuilder<EvmChain<EVMC_PETERSBURG>>{};
    }

    inline EvmBuilder<EvmChain<EVMC_ISTANBUL>> istanbul()
    {
        return EvmBuilder<EvmChain<EVMC_ISTANBUL>>{};
    }

    inline EvmBuilder<EvmChain<EVMC_BERLIN>> berlin()
    {
        return EvmBuilder<EvmChain<EVMC_BERLIN>>{};
    }

    inline EvmBuilder<EvmChain<EVMC_LONDON>> london()
    {
        return EvmBuilder<EvmChain<EVMC_LONDON>>{};
    }

    inline EvmBuilder<EvmChain<EVMC_PARIS>> paris()
    {
        return EvmBuilder<EvmChain<EVMC_PARIS>>{};
    }

    inline EvmBuilder<EvmChain<EVMC_SHANGHAI>> shanghai()
    {
        return EvmBuilder<EvmChain<EVMC_SHANGHAI>>{};
    }

    inline EvmBuilder<EvmChain<EVMC_CANCUN>> cancun()
    {
        return EvmBuilder<EvmChain<EVMC_CANCUN>>{};
    }

    inline EvmBuilder<EvmChain<EVMC_PRAGUE>> prague()
    {
        return EvmBuilder<EvmChain<EVMC_PRAGUE>>{};
    }

    inline EvmBuilder<EvmChain<EVMC_OSAKA>> osaka()
    {
        return EvmBuilder<EvmChain<EVMC_OSAKA>>{};
    }
}
