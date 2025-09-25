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

#include "account.hpp"
#include "state.hpp"

using namespace evmone::state;

namespace monad::vm::fuzzing
{
    bool is_account_erasable(evmc_revision const rev, Account const &acc);

    bool is_storage_erasable(StorageValue const &v);

    bool is_transient_storage_erasable(bytes32 const &v);
}
