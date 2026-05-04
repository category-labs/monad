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

#include <optional>
#include <string>

namespace monad::vm::utils
{
#ifdef MONAD_COMPILER_TESTING
    extern bool is_fuzzing_monad_vm;
#else
    static constexpr bool is_fuzzing_monad_vm = false;
#endif

#ifdef MONAD_COMPILER_STATS
    static constexpr bool collect_monad_compiler_stats = true;
#else
    static constexpr bool collect_monad_compiler_stats = false;
#endif

#ifdef MONAD_COMPILER_HOT_PATH_STATS
    static constexpr bool collect_monad_compiler_hot_path_stats = true;
#else
    static constexpr bool collect_monad_compiler_hot_path_stats = false;
#endif

#ifdef MONAD_COMPILER_TESTING
    extern bool is_compiler_runtime_debug_trace_enabled;
#else
    static constexpr bool is_compiler_runtime_debug_trace_enabled = false;
#endif

#ifdef MONAD_COMPILER_TESTING
    std::optional<std::string>
    make_compiler_asm_log_path(bytes32_t const &base_name);
#else
    __attribute__((always_inline)) constexpr std::optional<std::string>
    make_compiler_asm_log_path(bytes32_t const &)
    {
        return std::nullopt;
    }
#endif
}
