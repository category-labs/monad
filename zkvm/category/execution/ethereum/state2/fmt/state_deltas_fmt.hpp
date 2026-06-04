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

// zkVM shadow of category/execution/ethereum/state2/fmt/state_deltas_fmt.hpp.
// The host header provides quill copy_loggable + fmt::formatter
// specializations for StateDelta / StateDeltas / Code, used solely by the
// LOG_DEBUG calls inside BlockState. In the zkVM the LOG_* macros are
// no-ops (see zkvm/category/core/log.hpp), so the formatters never run —
// shadowing this header with an empty include avoids pulling the host's
// transitive int_fmt.hpp / account_fmt.hpp chain (which collides with
// intx's std::formatter specialization once `fmt` aliases to `std`).

#pragma once
