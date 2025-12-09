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

#include <category/core/config.hpp>
#include <evmc/evmc.h>

MONAD_NAMESPACE_BEGIN

struct AccessStats
{
    uint32_t warm_account_{0};
    uint32_t warm_storage_{0};
    uint32_t cold_account_{0};
    uint32_t cold_storage_{0};

    void event_account_access(evmc_access_status status)
    {
        if (status == EVMC_ACCESS_WARM) {
            warm_account_++;
        }
        else {
            cold_account_++;
        }
    }

    void event_storage_access(evmc_access_status status)
    {
        if (status == EVMC_ACCESS_WARM) {
            warm_storage_++;
        }
        else {
            cold_storage_++;
        }
    }
};

MONAD_NAMESPACE_END
