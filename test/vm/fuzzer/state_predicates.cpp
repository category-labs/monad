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
#include "state_predicates.hpp"

using namespace evmone::state;

namespace monad::vm::fuzzing
{
    // An erasable account is one that will be removed at the end of a transaction.
    // That is, it is empty and marked for erasure, or it has been destructed.
    // Empty accounts are deleted after every transaction. This is strictly
    // required until Byzantium where intermediate state root hashes are part of
    // the transaction receipt.
    // TODO: Consider limiting this only to Spurious Dragon.
    bool is_account_erasable(evmc_revision const rev, Account const &acc)
    {
        return (rev >= EVMC_SPURIOUS_DRAGON && acc.erase_if_empty && acc.is_empty())
                || acc.destructed;
    }

    bool is_storage_erasable(StorageValue const &v)
    {
        return v.current == evmc::bytes32{} && v.original == evmc::bytes32{} &&
                v.access_status == EVMC_ACCESS_COLD;
    }

    bool is_transient_storage_erasable(bytes32 const &v)
    {
        return v == evmc::bytes32{};
    }
}
