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

#include <category/execution/ethereum/db/util.hpp>
#include <category/vm/evm/monad/revision.h>

MONAD_NAMESPACE_BEGIN

struct MonadInMemoryMachine : public InMemoryMachine
{
    monad_revision revision{MONAD_ZERO};

    void set_revision(monad_revision rev)
    {
        revision = rev;
    }

    virtual mpt::Compute &get_compute() const override;
    virtual std::unique_ptr<mpt::StateMachine> clone() const override;
};

struct MonadOnDiskMachine : public OnDiskMachine
{
    monad_revision revision{MONAD_ZERO};

    void set_revision(monad_revision rev)
    {
        revision = rev;
    }

    virtual mpt::Compute &get_compute() const override;
    virtual std::unique_ptr<mpt::StateMachine> clone() const override;
};

MONAD_NAMESPACE_END
