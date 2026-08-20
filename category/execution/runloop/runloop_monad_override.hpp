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

#include <category/execution/ethereum/state2/state_deltas.hpp>

#include <cstdint>

MONAD_NAMESPACE_BEGIN

struct RunloopMonadOverrideMethods
{
    virtual ~RunloopMonadOverrideMethods() {}

    virtual uint64_t start_block_num() const = 0;
    virtual void
    preprocess_state_deltas(std::unique_ptr<StateDeltas> *) const = 0;
};

// Options to override monad runloop functionality. It is assumed that the
// runloop is only invoked a single time if `override_methods_` is `nullptr`.
class RunloopMonadOverride
{
    RunloopMonadOverrideMethods const *override_methods_;

public:
    RunloopMonadOverride(
        RunloopMonadOverrideMethods const *override_methods = nullptr)
        : override_methods_{override_methods}
    {
    }

    // Return the block number of the first block to be executed after opening
    // the database. The given `runloop_start` block number argument is
    // considered to be the first when `override_methods_` is `nullptr`.
    uint64_t start_block_num(uint64_t const runloop_start) const
    {
        if (MONAD_LIKELY(override_methods_ == nullptr)) {
            return runloop_start;
        }
        return override_methods_->start_block_num();
    }

    // Overrides the state deltas when `override_methods_` is not `nullptr`.
    void preprocess_state_deltas(std::unique_ptr<StateDeltas> *sd) const
    {
        if (MONAD_LIKELY(override_methods_ == nullptr)) {
            return;
        }
        override_methods_->preprocess_state_deltas(sd);
    }
};

MONAD_NAMESPACE_END
