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

#include <category/vm/evm/page_storage_status.h>

#include <evmc/evmc.h>

static_assert(
    sizeof(monad_page_storage_status) == sizeof(evmc_page_storage_status));

evmc_page_storage_status
to_evmc_page_storage_status(monad_page_storage_status const status)
{
    return {
        .first_page_write = status.first_page_write,
        .grew_state = status.grew_state};
}
