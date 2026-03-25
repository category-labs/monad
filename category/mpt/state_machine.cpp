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

#include <category/mpt/state_machine.hpp>

#include <category/mpt/detail/db_metadata.hpp>

MONAD_MPT_NAMESPACE_BEGIN

StorageFormat StateMachine::storage_format() const
{
    if (metadata_) {
        auto const fmt = metadata_->storage_format;
        return fmt == StorageFormat::PageCOO ? StorageFormat::PageCOO
                                             : StorageFormat::SlotCompact;
    }
    return StorageFormat::SlotCompact;
}

MONAD_MPT_NAMESPACE_END
