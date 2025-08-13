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
    #include <cstdlib>
    #include <cstring>

namespace monad::vm::utils
{
    static auto const is_fuzzing_monad_vm_env =
        std::getenv("MONAD_COMPILER_FUZZING");
    bool is_fuzzing_monad_vm = is_fuzzing_monad_vm_env &&
                               std::strcmp(is_fuzzing_monad_vm_env, "1") == 0;
}
#endif
