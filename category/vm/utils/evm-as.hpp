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

namespace monad::vm::utils::evm_as
{

    inline EvmBuilder<EvmTraits<EvmRevision::LatestStable>> latest()
    {
        return EvmBuilder<EvmTraits<EvmRevision::LatestStable>>{};
    }

    inline EvmBuilder<EvmTraits<constants::EARLIEST_SUPPORTED_EVM_FORK>>
    earliest()
    {
        return EvmBuilder<EvmTraits<constants::EARLIEST_SUPPORTED_EVM_FORK>>{};
    }

    inline EvmBuilder<EvmTraits<EvmRevision::Berlin>> berlin()
    {
        return EvmBuilder<EvmTraits<EvmRevision::Berlin>>{};
    }

    inline EvmBuilder<EvmTraits<EvmRevision::London>> london()
    {
        return EvmBuilder<EvmTraits<EvmRevision::London>>{};
    }

    inline EvmBuilder<EvmTraits<EvmRevision::Paris>> paris()
    {
        return EvmBuilder<EvmTraits<EvmRevision::Paris>>{};
    }

    inline EvmBuilder<EvmTraits<EvmRevision::Shanghai>> shanghai()
    {
        return EvmBuilder<EvmTraits<EvmRevision::Shanghai>>{};
    }

    inline EvmBuilder<EvmTraits<EvmRevision::Cancun>> cancun()
    {
        return EvmBuilder<EvmTraits<EvmRevision::Cancun>>{};
    }

    inline EvmBuilder<EvmTraits<EvmRevision::Prague>> prague()
    {
        return EvmBuilder<EvmTraits<EvmRevision::Prague>>{};
    }

    inline EvmBuilder<EvmTraits<EvmRevision::Osaka>> osaka()
    {
        return EvmBuilder<EvmTraits<EvmRevision::Osaka>>{};
    }

    inline EvmBuilder<EvmTraits<EvmRevision::Amsterdam>> amsterdam()
    {
        return EvmBuilder<EvmTraits<EvmRevision::Amsterdam>>{};
    }
}
