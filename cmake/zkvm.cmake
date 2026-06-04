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

# Apply RISC-V cross-compile compile options (warning suppressions, mirror
# include paths, bare-metal preprocessor definitions) to a target that has
# already had monad_compile_options applied. Only called in cross-compile
# mode — the x86 host build of monad-zkvm-guest-x86 doesn't need this.
function(monad_riscv_compile_options target)
    # GCC 15+ checks uninstantiated template bodies for errors
    # (-Wtemplate-body). This fires on constexpr-guarded AVX2 code paths
    # that are never instantiated on non-x86 targets.
    #
    # -Wno-unused-but-set-variable: the GCC 15.2 RISC-V backend false-positives
    # on values consumed only as a function-call argument (e.g. the CREATE2
    # code_hash in evm.cpp passed straight to create2_contract_address) —
    # identical source/flags compile clean with x86 GCC 15.2, so the host build
    # keeps the warning for real coverage.
    #
    # Gated on COMPILE_LANGUAGE:CXX — the flags are C++-only; applying them to
    # C TUs (e.g. assert.c) makes GCC emit a `command-line option ... is
    # valid for C++/ObjC++ but not for C` error under -Werror.
    target_compile_options(
        ${target} PRIVATE
        $<$<COMPILE_LANG_AND_ID:CXX,GNU>:-Wno-template-body>
        $<$<COMPILE_LANG_AND_ID:CXX,GNU>:-Wno-unused-but-set-variable>)

    # The shared shadow tree (zkvm/) is searched BEFORE MONAD_ROOT so that
    # zkVM-specific headers override their
    # host-tree counterparts.
    target_include_directories(${target}
        BEFORE PUBLIC "${ZKVM_INCLUDE_DIR}")
    target_include_directories(${target} PUBLIC "${MONAD_ROOT}")

    # NDEBUG: bare-metal zkVM has no libc, so __assert_func is missing.
    # _GLIBCXX_HAVE_ALIGNED_ALLOC: tells libstdc++ that our libc shim
    # (zkvm/core/libc.cpp) provides aligned_alloc; without it,
    # <cstdlib> does not expose std::aligned_alloc under newlib.
    target_compile_definitions(${target} PUBLIC
        NDEBUG _GLIBCXX_HAVE_ALIGNED_ALLOC)
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

# Remove the named libraries from a target's link interface.
function(monad_zkvm_drop_libraries target)
    foreach(prop LINK_LIBRARIES INTERFACE_LINK_LIBRARIES)
        get_target_property(_libs ${target} ${prop})
        if(_libs)
            foreach(lib ${ARGN})
                # PRIVATE deps appear in INTERFACE_LINK_LIBRARIES wrapped as
                # $<LINK_ONLY:lib>, so drop both the plain and wrapped forms.
                list(REMOVE_ITEM _libs "${lib}" "$<LINK_ONLY:${lib}>")
            endforeach()
            set_property(TARGET ${target} PROPERTY ${prop} ${_libs})
        endif()
    endforeach()
endfunction()

