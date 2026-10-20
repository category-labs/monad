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

#include <category/vm/utils/debug.hpp>

#include <array>
#include <chrono>
#include <cstdint>
#include <utility>

namespace monad::vm::runtime
{
    /// Wall-clock time of one VM call frame spent in the execution engine and
    /// in KECCAK256. Time in the host is not recorded. Scopes only read the
    /// clock in builds with MONAD_COMPILER_HOT_PATH_STATS.
    class EngineTimer
    {
    public:
        enum Section : uint8_t
        {
            Host,
            Engine,
            Keccak,
            NumSections
        };

        /// If stack_unwind skips the destructor, the call frame's Engine scope
        /// resets the timer when it ends.
        class Scope
        {
        public:
            [[gnu::always_inline]]
            Scope(EngineTimer &timer, Section const section) noexcept
                : timer_{timer}
            {
                if constexpr (utils::collect_monad_compiler_hot_path_stats) {
                    prev_ = timer_.enter(section);
                }
            }

            [[gnu::always_inline]]
            ~Scope()
            {
                if constexpr (utils::collect_monad_compiler_hot_path_stats) {
                    timer_.enter(prev_);
                }
            }

            Scope(Scope const &) = delete;
            Scope &operator=(Scope const &) = delete;

        private:
            EngineTimer &timer_;
            Section prev_{Host};
        };

        /// Charges the time since the last call to the current section, then
        /// makes `section` current. Returns the previous section.
        Section enter(Section const section) noexcept
        {
            auto const now = std::chrono::steady_clock::now();
            if (current_ != Host) {
                elapsed_[current_] += now - start_;
            }
            start_ = now;
            return std::exchange(current_, section);
        }

        std::chrono::nanoseconds elapsed(Section const section) const noexcept
        {
            return elapsed_[section];
        }

    private:
        std::chrono::steady_clock::time_point start_{};
        Section current_{Host};
        std::array<std::chrono::nanoseconds, NumSections> elapsed_{};
    };
}
