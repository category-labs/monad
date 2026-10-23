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

#pragma once

#include <category/core/config.hpp>
#include <category/execution/ethereum/db/util.hpp>
#include <category/mpt/compute.hpp>
#include <category/mpt/lbt/key_path.hpp>
#include <category/mpt/nibbles_view.hpp>
#include <category/mpt/state_machine.hpp>
#include <category/mpt/state_machine_kind.hpp>

#include <memory>

MONAD_NAMESPACE_BEGIN

// Commits the State table as a binary trie over page-encoded storage; every
// other table keeps the MPT commitment.
template <class Base>
struct LbtMachine final : public Base
{
    virtual mpt::state_machine_kind kind() const override;
    virtual std::unique_ptr<mpt::StateMachine> clone() const override;
    virtual void down(unsigned char nibble) override;
    virtual void down(mpt::NibblesView path) override;
    virtual mpt::Compute &get_compute() const override;

    // The key walked so far, from the start of the current account or storage
    // key down to depth. Requires table == State.
    mpt::NibblesView state_key_prefix() const;

private:
    mpt::lbt::KeyPath path_;
};

extern template struct LbtMachine<InMemoryMachine>;
extern template struct LbtMachine<OnDiskMachine>;

using LbtInMemoryMachine = LbtMachine<InMemoryMachine>;
using LbtOnDiskMachine = LbtMachine<OnDiskMachine>;

// Must run before an lbt_binary pool is opened through the metadata-driven Db
// constructor; otherwise create_state_machine() aborts.
void register_lbt_state_machines();

MONAD_NAMESPACE_END
