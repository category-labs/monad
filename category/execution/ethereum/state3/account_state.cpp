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

MONAD_NAMESPACE_BEGIN

StorageStatus AccountState::zero_out_key(
    bytes32_t const &key, bytes32_t const &original_value,
    bytes32_t const &current_value)
{
    auto const status = [&] {
        if (current_value == bytes32_t{}) {
            return StorageStatus::Assigned;
        }
        else if (original_value == current_value) {
            return StorageStatus::Deleted;
        }
        else if (original_value == bytes32_t{}) {
            return StorageStatus::AddedDeleted;
        }
        return StorageStatus::ModifiedDeleted;
    }();

    storage_ = storage_.insert({key, bytes32_t{}});

    return status;
}

StorageStatus AccountState::set_current_value(
    bytes32_t const &key, bytes32_t const &value,
    bytes32_t const &original_value, bytes32_t const &current_value)
{
    auto const status = [&] {
        if (current_value == bytes32_t{}) {
            if (original_value == bytes32_t{}) {
                return StorageStatus::Added;
            }
            else if (value == original_value) {
                return StorageStatus::DeletedRestored;
            }
            return StorageStatus::DeletedAdded;
        }
        else if (original_value == current_value && original_value != value) {
            return StorageStatus::Modified;
        }
        else if (original_value == value && original_value != current_value) {
            return StorageStatus::ModifiedRestored;
        }
        return StorageStatus::Assigned;
    }();

    storage_ = storage_.insert({key, value});

    return status;
}

MONAD_NAMESPACE_END
