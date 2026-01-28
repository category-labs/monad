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

#include <category/vm/evm/traits.hpp>
#include <category/vm/utils/evm-as/builder.hpp>
#include <category/vm/utils/evm-as/compiler.hpp>
#include <category/vm/utils/evm-as/instruction.hpp>
#include <category/vm/utils/evm-as/validator.hpp>

#include <evmc/evmc.h>

namespace monad::vm::utils::evm_as
{

    inline EvmBuilder<EvmTraits<EVMC_LATEST_STABLE_REVISION>> latest()
    {
        return EvmBuilder<EvmTraits<EVMC_LATEST_STABLE_REVISION>>{};
    }

    inline EvmBuilder<EvmTraits<EVMC_HOMESTEAD>> homestead()
    {
        return EvmBuilder<EvmTraits<EVMC_HOMESTEAD>>{};
    }

    inline EvmBuilder<EvmTraits<EVMC_TANGERINE_WHISTLE>> tangerine_whistle()
    {
        return EvmBuilder<EvmTraits<EVMC_TANGERINE_WHISTLE>>{};
    }

    inline EvmBuilder<EvmTraits<EVMC_SPURIOUS_DRAGON>> spurious_dragon()
    {
        return EvmBuilder<EvmTraits<EVMC_SPURIOUS_DRAGON>>{};
    }

    inline EvmBuilder<EvmTraits<EVMC_BYZANTIUM>> byzantium()
    {
        return EvmBuilder<EvmTraits<EVMC_BYZANTIUM>>{};
    }

    inline EvmBuilder<EvmTraits<EVMC_CONSTANTINOPLE>> constantinople()
    {
        return EvmBuilder<EvmTraits<EVMC_CONSTANTINOPLE>>{};
    }

    inline EvmBuilder<EvmTraits<EVMC_PETERSBURG>> petersburg()
    {
        return EvmBuilder<EvmTraits<EVMC_PETERSBURG>>{};
    }

    inline EvmBuilder<EvmTraits<EVMC_ISTANBUL>> istanbul()
    {
        return EvmBuilder<EvmTraits<EVMC_ISTANBUL>>{};
    }

    inline EvmBuilder<EvmTraits<EVMC_BERLIN>> berlin()
    {
        return EvmBuilder<EvmTraits<EVMC_BERLIN>>{};
    }

    inline EvmBuilder<EvmTraits<EVMC_LONDON>> london()
    {
        return EvmBuilder<EvmTraits<EVMC_LONDON>>{};
    }

    inline EvmBuilder<EvmTraits<EVMC_PARIS>> paris()
    {
        return EvmBuilder<EvmTraits<EVMC_PARIS>>{};
    }

    inline EvmBuilder<EvmTraits<EVMC_SHANGHAI>> shanghai()
    {
        return EvmBuilder<EvmTraits<EVMC_SHANGHAI>>{};
    }

    inline EvmBuilder<EvmTraits<EVMC_CANCUN>> cancun()
    {
        return EvmBuilder<EvmTraits<EVMC_CANCUN>>{};
    }

    inline EvmBuilder<EvmTraits<EVMC_PRAGUE>> prague()
    {
        return EvmBuilder<EvmTraits<EVMC_PRAGUE>>{};
    }

    inline EvmBuilder<EvmTraits<EVMC_OSAKA>> osaka()
    {
        return EvmBuilder<EvmTraits<EVMC_OSAKA>>{};
    }
}
