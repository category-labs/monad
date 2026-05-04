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

#ifdef MONAD_COMPILER_TESTING
    #include <category/core/assert.h>
    #include <category/core/bytes.hpp>
    #include <category/core/hex.hpp>

    #include <cstdlib>
    #include <cstring>
    #include <filesystem>
    #include <optional>
    #include <sstream>
    #include <string>

namespace monad::vm::utils
{
    static auto const is_fuzzing_monad_vm_env =
        std::getenv("MONAD_COMPILER_FUZZING");
    bool is_fuzzing_monad_vm = is_fuzzing_monad_vm_env &&
                               std::strcmp(is_fuzzing_monad_vm_env, "1") == 0;

    static auto const is_compiler_runtime_debug_trace_enabled_env =
        std::getenv("MONAD_COMPILER_DEBUG_TRACE");
    bool is_compiler_runtime_debug_trace_enabled =
        is_compiler_runtime_debug_trace_enabled_env &&
        std::strcmp(is_compiler_runtime_debug_trace_enabled_env, "1") == 0;

    std::optional<std::string>
    make_compiler_asm_log_path(bytes32_t const &base_name)
    {
        if (base_name == bytes32_t{}) {
            return std::nullopt;
        }
        static char const *debug_dir = std::getenv("MONAD_COMPILER_ASM_DIR");
        if (debug_dir) {
            MONAD_ASSERT(std::filesystem::is_directory(debug_dir));
            std::ostringstream file(std::ostringstream::ate);
            file.str(debug_dir);
            file << '/';
            file << to_hex(base_name);
            return file.str();
        }
        return std::nullopt;
    }
}
#endif
