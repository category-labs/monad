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

#include <category/execution/ethereum/state3/account_state.hpp>

#include <category/core/bytes.hpp>
#include <category/core/config.hpp>

#include <evmc/evmc.h>

MONAD_NAMESPACE_BEGIN

evmc_storage_status AccountState::zero_out_key(
    bytes32_t const &key, bytes32_t const &original_value,
    bytes32_t const &current_value)
{
    auto const status = [&] {
        if (current_value == bytes32_t{}) {
            return EVMC_STORAGE_ASSIGNED;
        }
        else if (original_value == current_value) {
            return EVMC_STORAGE_DELETED;
        }
        else if (original_value == bytes32_t{}) {
            return EVMC_STORAGE_ADDED_DELETED;
        }
        return EVMC_STORAGE_MODIFIED_DELETED;
    }();

    storage_[key] = bytes32_t{};

    return status;
}

evmc_storage_status AccountState::set_current_value(
    bytes32_t const &key, bytes32_t const &value,
    bytes32_t const &original_value, bytes32_t const &current_value)
{
    auto const status = [&] {
        if (current_value == bytes32_t{}) {
            if (original_value == bytes32_t{}) {
                return EVMC_STORAGE_ADDED;
            }
            else if (value == original_value) {
                return EVMC_STORAGE_DELETED_RESTORED;
            }
            return EVMC_STORAGE_DELETED_ADDED;
        }
        else if (original_value == current_value && original_value != value) {
            return EVMC_STORAGE_MODIFIED;
        }
        else if (original_value == value && original_value != current_value) {
            return EVMC_STORAGE_MODIFIED_RESTORED;
        }
        return EVMC_STORAGE_ASSIGNED;
    }();

    storage_[key] = value;

    return status;
}

MONAD_NAMESPACE_END
