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

    inline EvmBuilder<EvmTraits<MONAD_ETH_LATEST_STABLE_REVISION>> latest()
    {
        return EvmBuilder<EvmTraits<MONAD_ETH_LATEST_STABLE_REVISION>>{};
    }

    inline EvmBuilder<EvmTraits<constants::EARLIEST_SUPPORTED_EVM_FORK>>
    earliest()
    {
        return EvmBuilder<EvmTraits<constants::EARLIEST_SUPPORTED_EVM_FORK>>{};
    }

    inline EvmBuilder<EvmTraits<MONAD_ETH_CONSTANTINOPLE>> constantinople()
    {
        return EvmBuilder<EvmTraits<MONAD_ETH_CONSTANTINOPLE>>{};
    }

    inline EvmBuilder<EvmTraits<MONAD_ETH_PETERSBURG>> petersburg()
    {
        return EvmBuilder<EvmTraits<MONAD_ETH_PETERSBURG>>{};
    }

    inline EvmBuilder<EvmTraits<MONAD_ETH_ISTANBUL>> istanbul()
    {
        return EvmBuilder<EvmTraits<MONAD_ETH_ISTANBUL>>{};
    }

    inline EvmBuilder<EvmTraits<MONAD_ETH_BERLIN>> berlin()
    {
        return EvmBuilder<EvmTraits<MONAD_ETH_BERLIN>>{};
    }

    inline EvmBuilder<EvmTraits<MONAD_ETH_LONDON>> london()
    {
        return EvmBuilder<EvmTraits<MONAD_ETH_LONDON>>{};
    }

    inline EvmBuilder<EvmTraits<MONAD_ETH_PARIS>> paris()
    {
        return EvmBuilder<EvmTraits<MONAD_ETH_PARIS>>{};
    }

    inline EvmBuilder<EvmTraits<MONAD_ETH_SHANGHAI>> shanghai()
    {
        return EvmBuilder<EvmTraits<MONAD_ETH_SHANGHAI>>{};
    }

    inline EvmBuilder<EvmTraits<MONAD_ETH_CANCUN>> cancun()
    {
        return EvmBuilder<EvmTraits<MONAD_ETH_CANCUN>>{};
    }

    inline EvmBuilder<EvmTraits<MONAD_ETH_PRAGUE>> prague()
    {
        return EvmBuilder<EvmTraits<MONAD_ETH_PRAGUE>>{};
    }

    inline EvmBuilder<EvmTraits<MONAD_ETH_OSAKA>> osaka()
    {
        return EvmBuilder<EvmTraits<MONAD_ETH_OSAKA>>{};
    }
}
