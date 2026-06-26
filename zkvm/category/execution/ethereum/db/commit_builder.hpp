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

// zkVM replacement for category/execution/ethereum/db/commit_builder.hpp. The
// host class assembles an mpt::UpdateList for a live database commit; the guest
// has no such database — PartialTrieDb::commit walks the StateDeltas it is
// given and ignores the builder. Db::commit's signature still requires one, so
// the guest constructs this inert stand-in.
//
// Header-only and non-virtual on purpose. The host class puts its constructor
// and its vtable (keyed on add_state_deltas) in commit_builder.cpp, which the
// guest build drops along with the rest of the live-commit path; with no
// out-of-line member there is nothing left to link. Construction is the only
// thing the guest does with a builder, so it is the only thing declared here —
// any other use is a compile error rather than a silent no-op.

#include <category/core/config.hpp>

#include <cstdint>

MONAD_NAMESPACE_BEGIN

class CommitBuilder
{
public:
    explicit CommitBuilder(uint64_t) {}
};

MONAD_NAMESPACE_END
