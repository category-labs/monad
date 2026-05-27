# Copyright (C) 2025-26 Category Labs, Inc.
#
# This program is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 3 of the License, or
# (at your option) any later version.
#
# This program is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.
#
# You should have received a copy of the GNU General Public License
# along with this program.  If not, see <http://www.gnu.org/licenses/>.

# Helpers used by zkvm/CMakeLists.txt. Expects MONAD_ROOT to be set by the
# caller before invoking the functions below that use it.

# Apply the zkVM-specific compile options (warning suppressions, mirror
# include path, preprocessor definitions) to a target that has already had
# monad_compile_options applied.
function(monad_zkvm_compile_options target)
    # GCC 15+ checks uninstantiated template bodies for errors
    # (-Wtemplate-body). This fires on constexpr-guarded AVX2 code paths
    # that are never instantiated on non-x86 targets.
    target_compile_options(
        ${target} PRIVATE
        $<$<COMPILE_LANG_AND_ID:CXX,GNU>:-Wno-template-body>)

    target_include_directories(${target} BEFORE PUBLIC "${ZKVM_INCLUDE_DIR}")
    target_include_directories(${target} PUBLIC "${MONAD_ROOT}")

    # NDEBUG: bare-metal zkVM has no libc, so __assert_func is missing.
    # _GLIBCXX_HAVE_ALIGNED_ALLOC: tells libstdc++ that our libc shim
    # (zkvm/core/libc.cpp) provides aligned_alloc; without it,
    # <cstdlib> does not expose std::aligned_alloc under newlib.
    target_compile_definitions(${target} PUBLIC
        NDEBUG _GLIBCXX_HAVE_ALIGNED_ALLOC
        "MONAD_ZKVM_${_ZKVM_BACKEND_UPPER}")
endfunction()

# Remove entries from a target's SOURCES whose path ends with one of the
# given patterns. Used to strip host-only files (e.g. x86 assembly) from
# targets that are otherwise shared with the host build.
function(monad_zkvm_drop_sources target)
    get_target_property(_srcs ${target} SOURCES)
    set(_kept "")
    foreach(s ${_srcs})
        set(_drop OFF)
        foreach(pat ${ARGN})
            if(s MATCHES "(^|/)${pat}$")
                set(_drop ON)
                break()
            endif()
        endforeach()
        if(NOT _drop)
            list(APPEND _kept "${s}")
        endif()
    endforeach()
    set_property(TARGET ${target} PROPERTY SOURCES ${_kept})
endfunction()

