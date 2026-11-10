// Copyright (C) 2025-26 Category Labs, Inc.
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

#include <category/core/assert.h>
#include <category/core/config.hpp>
#include <category/vm/evm/revision.hpp>

MONAD_NAMESPACE_BEGIN

char const *to_string(EvmRevision const rev)
{
    switch (rev) {
    case EvmRevision::Frontier:
        return "Frontier";
    case EvmRevision::Homestead:
        return "Homestead";
    case EvmRevision::TangerineWhistle:
        return "TangerineWhistle";
    case EvmRevision::SpuriousDragon:
        return "SpuriousDragon";
    case EvmRevision::Byzantium:
        return "Byzantium";
    case EvmRevision::Constantinople:
        return "Constantinople";
    case EvmRevision::Petersburg:
        return "Petersburg";
    case EvmRevision::Istanbul:
        return "Istanbul";
    case EvmRevision::Berlin:
        return "Berlin";
    case EvmRevision::London:
        return "London";
    case EvmRevision::Paris:
        return "Paris";
    case EvmRevision::Shanghai:
        return "Shanghai";
    case EvmRevision::Cancun:
        return "Cancun";
    case EvmRevision::Prague:
        return "Prague";
    case EvmRevision::Osaka:
        return "Osaka";
    case EvmRevision::Amsterdam:
        return "Amsterdam";
    case EvmRevision::Experimental:
        return "Experimental";
    }
    MONAD_ABORT("unhandled EvmRevision");
}

MONAD_NAMESPACE_END
