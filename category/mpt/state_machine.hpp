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

#include <category/mpt/config.hpp>

#include <memory>
#include <stddef.h>

MONAD_MPT_NAMESPACE_BEGIN

struct Compute;

namespace detail
{
    struct db_metadata;
}

// Persisted in db_metadata. Values must be stable.
enum class StorageFormat : uint8_t
{
    SlotCompact = 0,
    PageCOO = 1,
};

struct StateMachine
{
    virtual ~StateMachine() = default;
    virtual std::unique_ptr<StateMachine> clone() const = 0;
    virtual void down(unsigned char nibble) = 0;
    virtual void up(size_t) = 0;
    virtual Compute &get_compute() const = 0;
    virtual bool cache() const = 0;
    virtual bool compact() const = 0;
    virtual bool is_variable_length() const = 0;

    virtual bool auto_expire() const
    {
        return false;
    }

    // Live read from db_metadata when backed by an on-disk DB.
    // Returns SlotCompact for in-memory DBs or uninitialised metadata.
    StorageFormat storage_format() const;

    void bind_metadata(detail::db_metadata const *m)
    {
        metadata_ = m;
    }

private:
    detail::db_metadata const *metadata_{nullptr};
};

MONAD_MPT_NAMESPACE_END
