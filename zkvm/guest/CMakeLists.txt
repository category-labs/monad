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

# The monad zkVM guest library. Two modes:
#
# 1. Cross-compile (RISC-V): invoked standalone as the top-level CMake
#    project (via `cmake -S zkvm/guest ...`, typically from the build-support
#    crate). The caller sets MONAD_ZKVM_GUEST_TARGET to a backend suffix
#    (zisk or sp1) — used only to name the resulting archive
#    (monad-zkvm-guest-<suffix>). This file drives the full bare-metal
#    build — third-party deps, monad-vm-* libs (with .S drops),
#    libc/libstdcxx stubs, setjmp extraction — and bundles everything into
#    a single STATIC archive.
#
# 2. Host x86: invoked from the root host CMakeLists.txt via
#    add_subdirectory(zkvm/guest). MONAD_ZKVM_GUEST_TARGET is not set;
#    this file builds the monad-zkvm-x86-test-runner executable directly
#    from ffi.cpp + x86_test_runner.cpp linked against the host's existing
#    monad_execution target. No intermediate static library.

cmake_minimum_required(VERSION 3.20)

if(DEFINED MONAD_ZKVM_GUEST_TARGET)
    # ---- Cross-compile mode ----

    project(monad-zkvm-guest LANGUAGES C CXX ASM)

    if(NOT MONAD_ZKVM_GUEST_TARGET MATCHES "^(zisk|sp1)$")
        message(FATAL_ERROR
            "MONAD_ZKVM_GUEST_TARGET must be 'zisk' or 'sp1', got "
            "'${MONAD_ZKVM_GUEST_TARGET}'")
    endif()
    if(MONAD_COMPILER_TESTING)
        message(FATAL_ERROR
            "MONAD_COMPILER_TESTING is not supported in zkVM builds")
    endif()

    # Fail-closed identity for report/release ZisK artifacts. This baseline
    # deliberately certifies only properties already present on the Sam/ZisK
    # 1.2 branch. A later optimisation that depends on a build switch, compiler
    # extension or runtime precompile must append its name to
    # _monad_zkvm_official_features and extend the post-link audit in the same
    # commit. Ordinary source changes need no feature bit: the embedded full
    # Git commit and the ELF digest already identify them.
    option(MONAD_ZKVM_OFFICIAL_PROFILE
           "build the audited, fail-closed official ZisK guest profile" OFF)
    set(_monad_zkvm_official_features "baseline" "zisk-dma")
    set(_monad_zkvm_runtime_version "1.2.0-alpha")
    set(_monad_zkvm_runtime_revision
        "fbbc69bcd2ea9a78d1a438b4a897bc48ff0b00a3")
    if(MONAD_ZKVM_OFFICIAL_PROFILE AND
       NOT MONAD_ZKVM_GUEST_TARGET STREQUAL "zisk")
        message(FATAL_ERROR
            "MONAD_ZKVM_OFFICIAL_PROFILE is a ZisK-only build profile")
    endif()

    # The feature list above is a claim about the binary; on its own nothing
    # holds the build to it. A lever the profile depends on is named there and
    # listed here, and this forces it ON and refuses an explicit OFF, so the
    # signature cannot describe a guest that was built without it. A commit
    # adding a lever appends to both lists.
    set(_monad_zkvm_required_levers MONAD_ZKVM_ZISK_DMA)
    if(MONAD_ZKVM_OFFICIAL_PROFILE)
        foreach(_lever ${_monad_zkvm_required_levers})
            if(DEFINED ${_lever} AND NOT ${_lever})
                message(FATAL_ERROR
                    "${_lever}=OFF contradicts MONAD_ZKVM_OFFICIAL_PROFILE=ON")
            endif()
            set(${_lever} ON CACHE BOOL
                "required by the official ZisK profile" FORCE)
        endforeach()
    endif()

    # The riscv64-elf toolchain file specifies these as CMAKE_*_FLAGS_INIT,
    # but cmake-rs (driving this cmake invocation from build.rs) overrides
    # CMAKE_*_FLAGS with cc-rs's target-arch flags only — dropping the
    # bare-metal / C++ABI knobs. Append them here so they're applied
    # regardless of who set the initial flags.
    string(APPEND CMAKE_C_FLAGS
        " -mcmodel=medany -nostartfiles -nostdlib")
    string(APPEND CMAKE_CXX_FLAGS
        " -mcmodel=medany -nostartfiles -nostdlib++ -fno-exceptions -fno-rtti")

    # ZisK-only codegen flags.
    #  - -march adds Zbb/Zbs/Zbkb, transpiled natively by ZisK >= v1.2.0-alpha.
    #  - -fno-pic: cmake-rs injects cc-rs's -fPIC, but the guest is a
    #    statically linked fixed-address ELF, so PIC only buys GOT
    #    indirections on global accesses.
    #
    # These are appended (not set via CMAKE_*_FLAGS_INIT) because cmake-rs
    # overrides CMAKE_*_FLAGS, and the -march must land after cc-rs's
    # -march=rv64ima — the last flag wins.
    if(MONAD_ZKVM_GUEST_TARGET STREQUAL "zisk")
        set(_zisk_march "-march=rv64ima_zicsr_zbb_zbs_zbkb -mabi=lp64")
        string(APPEND CMAKE_C_FLAGS " ${_zisk_march} -fno-pic")
        string(APPEND CMAKE_CXX_FLAGS " ${_zisk_march} -fno-pic")
        string(APPEND CMAKE_ASM_FLAGS " ${_zisk_march}")
    endif()

    # Let the inliner grow the program. GCC's -O3 defaults are tuned for a binary that has to fit a
    # cache and share a machine; a zkVM guest pays per executed instruction and nothing at all for
    # size, so the trade the defaults make is the wrong one here.
    #
    # This is the largest single lever measured on the axis, and it changes no source. Outside the
    # interpreter -- which is at parity -- we execute 44.7 M steps a block against ziskethone's
    # 33.7 M, 85 % of the whole COST gap, in 1.64x as many function calls at 0.81x their steps per
    # call; our ELF carries 2,540 live symbols against their 613. That is call granularity, spread
    # across everything, and the inliner is the only tool that reaches all of it at once.
    #
    # Measured on the canonical 200 blocks, each point its own A/B:
    #   unit-growth 250  / auto 90  / min-speedup 5 : -0.65 % steps, -0.33 % COST, 2,432 symbols
    #   unit-growth 800  / auto 200 / min-speedup 1 : -1.65 % steps, -0.85 % COST, 2,394 symbols
    #   unit-growth 3000 / auto 500 / min-speedup 0 : -1.82 % steps, -0.97 % COST, 2,351 symbols
    # The curve saturates: the third point buys 0.12 points more for four times the parameters and
    # 33 % more binary. The second is taken. ROM usage is not the constraint at either -- 7.9 %
    # against the default build's 6.8 %, of a budget the default already uses a fifteenth of.
    #
    # A unity build was tried first and REGRESSED, +1.35 % COST, which is why the mechanism is stated
    # as "let it grow" and not "let it see more": batching translation units exhausts the same budget
    # instead of widening it, and the symbol count did not move (2,540 -> 2,545) while the ratio got
    # worse. Do not re-try it without raising these first.
    #
    # These land in CMAKE_CXX_FLAGS deliberately: the official profile signs
    # SHA256(compiler, CMAKE_{C,CXX}_FLAGS[_RELEASE]), so a codegen change that did not enter that
    # string would leave two different guests claiming one identity.
    string(APPEND CMAKE_CXX_FLAGS
        " --param inline-unit-growth=800"
        " --param large-function-growth=1500"
        " --param max-inline-insns-auto=200"
        " --param max-inline-insns-single=800"
        " --param inline-min-speedup=1"
        " -finline-functions"
        " -funroll-loops")

    set(_guest_target "monad-zkvm-guest-${MONAD_ZKVM_GUEST_TARGET}")

    # Expose the backend as a compile definition, for the places where the two
    # diverge: the ripemd160 accelerators place the digest at opposite ends of
    # their 32-byte output word, so the precompile shim normalises them
    # differently (zkvm/category/execution/ethereum/precompiles_impl.hpp), and
    # the Keccak-f[1600] precompile is reached by a different entry on each
    # (zkvm/category/crypto/keccakf1600.h).
    if(MONAD_ZKVM_GUEST_TARGET STREQUAL "sp1")
        add_compile_definitions(MONAD_ZKVM_SP1)
    elseif(MONAD_ZKVM_GUEST_TARGET STREQUAL "zisk")
        add_compile_definitions(MONAD_ZKVM_ZISK)
        # GCC's default tuning for this target is -mtune=rocket, whose cost
        # model says an unaligned access is slow, so a 4-byte load through a
        # 1-aligned pointer becomes nine instructions instead of one. The
        # guest reads 4-byte child ids out of a witness blob that never aligns
        # them, so it pays that everywhere. ZisK executes the unaligned load
        # directly -- 504 of 504 corpus blocks give byte-identical public
        # values with this on.
        #
        # ZisK only: the SP1 emulator's handling of unaligned access has not
        # been established, and the same flag there would be a guess.
        #
        # Here rather than lower down: the official profile signs
        # CMAKE_{C,CXX}_FLAGS, and a flag appended after that signature would
        # leave two differently-built guests claiming one identity.
        string(APPEND CMAKE_C_FLAGS " -mtune=generic-ooo")
        string(APPEND CMAKE_CXX_FLAGS " -mtune=generic-ooo")

        # Block memory operations through ZisK's DMA precompile, rather than a
        # call into the ziskos mem* thunk or an inline load/store run.
        #
        # It reaches copies no source change can: evmc_bytes32 is uint8_t[32]
        # with alignment 1, so a plain struct assignment cannot use word moves
        # and gcc emits a libcall -- with a frame, and the arguments marshalled
        # into a0/a1/a2. The marker takes the same copy in one instruction.
        #
        # It needs the patched compiler this repo carries: build one with
        # zkvm/toolchain/zisk-dma-gcc/build-gcc15.sh and point
        # RISCV_TOOLCHAIN_DIR at it. A stock compiler rejects the flag outright
        # rather than ignoring it, and the official profile probes the lowering
        # besides, so a build that forgets the toolchain fails loudly.
        #
        # The lowering emits `csrs 0x813,src`, which the assembler rejects
        # unless Zicsr is named -- _zisk_march above carries it.
        option(MONAD_ZKVM_ZISK_DMA
               "lower block mem* to the ZisK DMA precompile" OFF)
        if(MONAD_ZKVM_ZISK_DMA)
            string(APPEND CMAKE_C_FLAGS " -mzisk-dma")
            string(APPEND CMAKE_CXX_FLAGS " -mzisk-dma")
        endif()
    endif()

    if(MONAD_ZKVM_OFFICIAL_PROFILE)
        if(NOT CMAKE_CXX_COMPILER_ID STREQUAL "GNU" OR
           NOT CMAKE_CXX_COMPILER_VERSION VERSION_EQUAL "15.2.0")
            message(FATAL_ERROR
                "initial official ZisK 1.2 profile requires GCC 15.2.0; got "
                "${CMAKE_CXX_COMPILER_ID} ${CMAKE_CXX_COMPILER_VERSION}")
        endif()
        if(NOT DEFINED MONAD_ZKVM_GIT_COMMIT)
            message(FATAL_ERROR
                "official ZisK profile requires MONAD_ZKVM_GIT_COMMIT")
        endif()
        string(LENGTH "${MONAD_ZKVM_GIT_COMMIT}" _official_git_commit_length)
        if(NOT _official_git_commit_length EQUAL 40 OR
           NOT MONAD_ZKVM_GIT_COMMIT MATCHES "^[0-9a-f]+$")
            message(FATAL_ERROR
                "MONAD_ZKVM_GIT_COMMIT must be a full lowercase Git SHA")
        endif()

        # The DMA lowering is not in upstream gcc; it comes from the patch set in
        # zkvm/toolchain/zisk-dma-gcc. Keyed on the flag actually being in the
        # flags rather than on the option that sets it, so the assertion holds
        # for any route to -mzisk-dma and needs no maintenance when one is added.
        #
        # Hashing the compiler binary cannot stand in for this. Two people
        # applying the same patch to the same source get different binaries --
        # different host compiler, build paths, linked libraries -- so the hash
        # below is provenance and not a gate: it is recorded, never compared.
        # What is checkable is the behaviour, and only the emitted marker shows
        # it. The flag parses on a stock compiler that ignores it.
        if(CMAKE_CXX_FLAGS MATCHES "-mzisk-dma" OR CMAKE_C_FLAGS MATCHES "-mzisk-dma")
            # Compiled with the guest's own flags, so the probe tests the
            # configuration being built and not a neighbouring one -- the
            # lowering needs Zicsr, which only those flags carry. `sink` keeps
            # the copy alive; at -O2 a dead memcpy lowers to nothing and the
            # probe would report a stock compiler as patched.
            set(_dma_probe "${CMAKE_CURRENT_BINARY_DIR}/zisk-dma-probe.c")
            file(WRITE "${_dma_probe}"
                "void *memcpy(void *, void const *, unsigned long);\n"
                "void sink(void *);\n"
                "void p(char *d, char const *s) { memcpy(d, s, 512); sink(d); }\n")
            separate_arguments(_dma_probe_flags UNIX_COMMAND "${CMAKE_C_FLAGS}")
            execute_process(
                COMMAND ${CMAKE_C_COMPILER} ${_dma_probe_flags} -O2 -S -o -
                        "${_dma_probe}"
                RESULT_VARIABLE _dma_rc OUTPUT_VARIABLE _dma_asm ERROR_QUIET)
            if(NOT _dma_rc EQUAL 0)
                message(FATAL_ERROR
                    "-mzisk-dma is in the flags but ${CMAKE_C_COMPILER} cannot "
                    "compile with it; build the compiler with "
                    "zkvm/toolchain/zisk-dma-gcc/build-gcc15.sh")
            endif()
            if(NOT _dma_asm MATCHES "csrs?[ \t]+[^\n]*0x813")
                message(FATAL_ERROR
                    "${CMAKE_C_COMPILER} accepts -mzisk-dma but emits no DMA "
                    "marker, so block mem* would still be thunk calls. Build it "
                    "with zkvm/toolchain/zisk-dma-gcc/build-gcc15.sh")
            endif()
        endif()
    endif()

    # Repo + third-party paths.
    set(MONAD_ROOT "${CMAKE_CURRENT_SOURCE_DIR}/../..")
    set(CATEGORY_MAIN_DIR "${MONAD_ROOT}")
    set(THIRD_PARTY_DIR "${MONAD_ROOT}/third_party")
    set(ZKVM_INCLUDE_DIR "${MONAD_ROOT}/zkvm")

    include("${MONAD_ROOT}/cmake/compile_options.cmake")
    include("${MONAD_ROOT}/cmake/zkvm.cmake")

    # ---- Third-party dependencies (minimal for bare-metal) ----

    # Boost.Outcome (header-only) is used via category/core/result.hpp.
    # Mirror the host build's discovery (CMakeLists.txt:67) but without any
    # compiled COMPONENTS — those won't link for RISC-V.
    #
    # The cross-compile toolchain sets CMAKE_SYSTEM_NAME=Generic, which
    # disables CMAKE_LIBRARY_ARCHITECTURE; that means find_package won't
    # search the Ubuntu multi-arch path /usr/lib/x86_64-linux-gnu/cmake/Boost-*
    # where the system BoostConfig.cmake actually lives. Locate it ourselves
    # and set Boost_DIR before delegating to find_package.
    if(NOT DEFINED Boost_DIR)
        file(GLOB _boost_cmake_dirs
            "/usr/lib/x86_64-linux-gnu/cmake/Boost-*"
            "/usr/lib/cmake/Boost-*"
            "/usr/lib64/cmake/Boost-*"
            "/usr/local/lib/cmake/Boost-*")
        foreach(_d IN LISTS _boost_cmake_dirs)
            if(EXISTS "${_d}/BoostConfig.cmake")
                set(Boost_DIR "${_d}")
                break()
            endif()
        endforeach()
    endif()
    find_package(Boost CONFIG REQUIRED)
    # Boost::headers's INTERFACE_INCLUDE_DIRECTORIES is /usr/include — that
    # dir contains glibc headers (<stdint.h>, <linux/types.h>) that would
    # hijack the RISC-V cross-toolchain's own copies if searched before them.
    # Even -isystem puts the path before the compiler's built-in dirs, so use
    # -idirafter to search /usr/include *last* — only <boost/...> resolves
    # from there since the cross-toolchain doesn't ship Boost.
    get_target_property(_boost_inc Boost::headers INTERFACE_INCLUDE_DIRECTORIES)

    add_subdirectory("${THIRD_PARTY_DIR}/unordered_dense" unordered_dense)

    # cthash — header-only constexpr hashing, used by abi_signatures.hpp
    # for compile-time ABI selector derivation. Has its own add_subdirectory
    # CMakeLists, exposes the include dir on the cthash target.
    if(NOT TARGET cthash)
        add_subdirectory("${THIRD_PARTY_DIR}/cthash" cthash SYSTEM)
    endif()

    # immer — header-only, used by category/execution/ethereum/state3/.
    # Mirrors the immer options set in the root CMakeLists.txt.
    option(immer_BUILD_TESTS OFF)
    option(immer_BUILD_EXAMPLES OFF)
    option(immer_BUILD_EXTRAS OFF)
    add_subdirectory("${THIRD_PARTY_DIR}/immer" immer SYSTEM)

    # komihash — header-only, used by category/core/bytes_hash_compare.hpp.
    # Mirrors root CMakeLists.txt:138.
    if(NOT TARGET komihash)
        add_library(komihash INTERFACE)
        target_include_directories(komihash INTERFACE "${THIRD_PARTY_DIR}/komihash")
    endif()

    # nlohmann_json — header-only. The guest only needs the forward-declaration
    # header (json_fwd.hpp): call_frame.hpp / db/util.hpp forward-declare
    # nlohmann::json, and the TUs that actually serialise (call_frame.cpp,
    # db/util.cpp, ...) are dropped from the guest build. Providing just the
    # include dir keeps the full library out of the bare-metal build.
    if(NOT TARGET nlohmann_json::nlohmann_json)
        add_library(nlohmann_json INTERFACE)
        add_library(nlohmann_json::nlohmann_json ALIAS nlohmann_json)
        target_include_directories(nlohmann_json INTERFACE
            "${THIRD_PARTY_DIR}/nlohmann_json/include")
    endif()

    # blst — header-only INTERFACE in zkVM mode. precompiles_bls12.hpp
    # unconditionally `#include`s <blst.h> for the type aliases, but no
    # surviving zkVM TU calls a blst_* function — the host
    # precompiles_bls12.cpp is dropped in favour of the zkVM shadow, which
    # only provides the msm_discount gas tables. So no link symbols are
    # needed; just the header on the include path.
    if(NOT TARGET blst)
        add_library(blst INTERFACE)
        add_library(blst::blst ALIAS blst)
        target_include_directories(blst INTERFACE "${THIRD_PARTY_DIR}/blst/bindings")
    endif()

    set(EVMC_INCLUDE_DIR "${THIRD_PARTY_DIR}/evmc/include")
    add_library(evmc INTERFACE)
    add_library(evmc::evmc ALIAS evmc)
    target_compile_features(evmc INTERFACE c_std_99)
    target_include_directories(evmc INTERFACE ${EVMC_INCLUDE_DIR})

    # ---- VM component libraries ----

    # Stub for monad-vm-utils — the interpreter unconditionally links it, but
    # the utils library itself is not buildable in the zkVM environment (TBB,
    # Boost, etc.). Header-only utils used by the interpreter (debug.hpp,
    # traits.hpp, scope_exit.hpp) are reached via the MONAD_ROOT include
    # path added by monad_riscv_compile_options.
    add_library(monad-vm-utils INTERFACE)
    add_library(monad-vm::monad-vm-utils ALIAS monad-vm-utils)

    add_subdirectory("${MONAD_ROOT}/category/vm/evm" evm)
    add_subdirectory("${MONAD_ROOT}/category/vm/runtime" runtime)
    add_subdirectory("${MONAD_ROOT}/category/vm/interpreter" interpreter)

    # Strip x86-only assembly from the otherwise shared targets.
    monad_zkvm_drop_sources(monad-vm-runtime
        "context.S" "exit.S" "math.S" "transmute.S")
    monad_zkvm_drop_sources(monad-vm-interpreter "entry.S")

    foreach(tgt monad-vm-evm monad-vm-runtime monad-vm-interpreter)
        monad_riscv_compile_options(${tgt})
        target_link_libraries(${tgt} PUBLIC unordered_dense)
    endforeach()

    # ---- Extract setjmp/longjmp from the compiler's newlib libc.a ----

    # The query must carry the same -march/-mabi as the compile, or a multilib
    # toolchain answers with its default variant — on an rv32 default that is a
    # libc.a whose objects the rv64 link rejects as "incompatible with
    # elf64-littleriscv".
    separate_arguments(_arch_query UNIX_COMMAND "${CMAKE_C_FLAGS}")

    execute_process(
        COMMAND ${CMAKE_C_COMPILER} ${_arch_query} -print-file-name=libc.a
        OUTPUT_VARIABLE _libc_a
        OUTPUT_STRIP_TRAILING_WHITESPACE
    )

    set(_newlib_dir "${CMAKE_CURRENT_BINARY_DIR}/_libc_objs")
    file(MAKE_DIRECTORY "${_newlib_dir}")

    if(EXISTS "${_libc_a}")
        # Extract objects we need from newlib's libc.a. Listed individually
        # rather than -all-extract so we don't drag in heavy initialisation
        # objects (atexit, malloc, syscalls) that the zkVM stubs replace.
        # Add more here as the link surface grows; each entry is the object
        # file name inside libc.a as produced by `ar t`.
        set(_libc_obj_names
            "libc_a-setjmp.o"
            "libc_a-strcmp.o"
        )
        foreach(_obj IN LISTS _libc_obj_names)
            execute_process(
                COMMAND ${CMAKE_AR} x "${_libc_a}" "${_obj}"
                WORKING_DIRECTORY "${_newlib_dir}"
            )
        endforeach()
        file(GLOB _libc_objs "${_newlib_dir}/*.o")
        if(NOT _libc_objs)
            message(FATAL_ERROR
                "Failed to extract any objects from ${_libc_a}")
        endif()
    else()
        message(FATAL_ERROR
            "libc.a not found via compiler query")
    endif()

    # ---- Extract __popcountdi2 from the compiler's libgcc.a ----
    # immer's HAMT bit math needs __popcountdi2
    execute_process(
        COMMAND ${CMAKE_C_COMPILER} ${_arch_query} -print-libgcc-file-name
        OUTPUT_VARIABLE _libgcc_a
        OUTPUT_STRIP_TRAILING_WHITESPACE
    )
    set(_libgcc_dir "${CMAKE_CURRENT_BINARY_DIR}/_libgcc_objs")
    file(MAKE_DIRECTORY "${_libgcc_dir}")
    if(EXISTS "${_libgcc_a}")
        execute_process(
            COMMAND ${CMAKE_AR} x "${_libgcc_a}" "_popcountsi2.o"
            WORKING_DIRECTORY "${_libgcc_dir}"
        )
        file(GLOB _libgcc_objs "${_libgcc_dir}/*.o")
        if(NOT _libgcc_objs)
            message(FATAL_ERROR
                "Failed to extract __popcountdi2 from ${_libgcc_a}")
        endif()
    else()
        message(FATAL_ERROR
            "libgcc.a not found via compiler query")
    endif()

    # The profile's identity is computed here, at the bottom of the flag setup
    # and above the first compiled target. It signs CMAKE_{C,CXX,ASM}_FLAGS, so a
    # flag appended below this point would be in the guest and not in its
    # signature, and two differently-built guests would claim one identity.
    # A commit that adds a guest flag adds it above this block.
    if(MONAD_ZKVM_OFFICIAL_PROFILE)
        file(SHA256 "${CMAKE_CXX_COMPILER}" _official_cxx_sha256)
        # The patch files hash the same on every machine, unlike the compiler
        # they produce, so this is the part of the toolchain identity that two
        # builds of one commit can actually be expected to agree on.
        set(_dma_patch_dir "${CMAKE_CURRENT_SOURCE_DIR}/../toolchain/zisk-dma-gcc")
        set(_dma_patch_sha "")
        foreach(_p 0001-riscv-zisk-dma-lowering-14.3.0.patch
                   0002-riscv.md-forward-port-15.2.0.diff
                   0003-guest-zicsr-15.2.0.patch)
            if(NOT EXISTS "${_dma_patch_dir}/${_p}")
                message(FATAL_ERROR
                    "official ZisK profile: missing ${_p} in zkvm/toolchain/zisk-dma-gcc")
            endif()
            file(SHA256 "${_dma_patch_dir}/${_p}" _one)
            string(APPEND _dma_patch_sha "${_one}")
        endforeach()
        string(SHA256 _dma_patch_sha "${_dma_patch_sha}")
        list(JOIN _monad_zkvm_official_features "," _official_features_csv)
        string(SHA256 _official_build_signature
            "${_official_cxx_sha256}\n${CMAKE_C_FLAGS}\n${CMAKE_C_FLAGS_RELEASE}\n${CMAKE_CXX_FLAGS}\n${CMAKE_CXX_FLAGS_RELEASE}\n${CMAKE_ASM_FLAGS}\n${CMAKE_ASM_FLAGS_RELEASE}\n${_monad_zkvm_runtime_revision}\n${_official_features_csv}\n${_dma_patch_sha}")
        add_compile_definitions(
            MONAD_ZKVM_OFFICIAL_PROFILE=1
            MONAD_ZKVM_BUILD_COMMIT="${MONAD_ZKVM_GIT_COMMIT}"
            MONAD_ZKVM_BUILD_SIGNATURE="${_official_build_signature}"
            MONAD_ZKVM_BUILD_FEATURES="${_official_features_csv}"
            MONAD_ZKVM_RUNTIME_VERSION="${_monad_zkvm_runtime_version}")
        file(WRITE "${CMAKE_BINARY_DIR}/monad-zkvm-official-profile.json"
            "{\n"
            "  \"schema\": 2,\n"
            "  \"profile\": \"official\",\n"
            "  \"target\": \"zisk\",\n"
            "  \"runtime_version\": \"${_monad_zkvm_runtime_version}\",\n"
            "  \"runtime_revision\": \"${_monad_zkvm_runtime_revision}\",\n"
            "  \"features_csv\": \"${_official_features_csv}\",\n"
            "  \"compiler\": \"${CMAKE_CXX_COMPILER}\",\n"
            "  \"compiler_id\": \"${CMAKE_CXX_COMPILER_ID}\",\n"
            "  \"compiler_version\": \"${CMAKE_CXX_COMPILER_VERSION}\",\n"
            "  \"compiler_sha256\": \"${_official_cxx_sha256}\",\n"
            "  \"dma_patch_sha256\": \"${_dma_patch_sha}\",\n"
            "  \"commit\": \"${MONAD_ZKVM_GIT_COMMIT}\",\n"
            "  \"build_signature\": \"${_official_build_signature}\",\n"
            "  \"c_flags\": \"${CMAKE_C_FLAGS}\",\n"
            "  \"c_flags_release\": \"${CMAKE_C_FLAGS_RELEASE}\",\n"
            "  \"cxx_flags\": \"${CMAKE_CXX_FLAGS}\",\n"
            "  \"cxx_flags_release\": \"${CMAKE_CXX_FLAGS_RELEASE}\",\n"
            "  \"asm_flags\": \"${CMAKE_ASM_FLAGS}\",\n"
            "  \"asm_flags_release\": \"${CMAKE_ASM_FLAGS_RELEASE}\"\n"
            "}\n")
    else()
        # A guest built without the profile must say so. Left silent it is
        # indistinguishable from an audited one to everything downstream --
        # the runner, a report, a verifier -- and the difference is the whole
        # point of having a profile. The manifest is written in both modes so
        # that its absence never has to be interpreted.
        add_compile_definitions(MONAD_ZKVM_DEV_PROFILE=1)
        file(WRITE "${CMAKE_BINARY_DIR}/monad-zkvm-official-profile.json"
            "{\n"
            "  \"schema\": 2,\n"
            "  \"profile\": \"dev\",\n"
            "  \"target\": \"${MONAD_ZKVM_GUEST_TARGET}\",\n"
            "  \"compiler\": \"${CMAKE_CXX_COMPILER}\",\n"
            "  \"compiler_id\": \"${CMAKE_CXX_COMPILER_ID}\",\n"
            "  \"compiler_version\": \"${CMAKE_CXX_COMPILER_VERSION}\",\n"
            "  \"c_flags\": \"${CMAKE_C_FLAGS}\",\n"
            "  \"cxx_flags\": \"${CMAKE_CXX_FLAGS}\",\n"
            "  \"asm_flags\": \"${CMAKE_ASM_FLAGS}\"\n"
            "}\n")
    endif()

    # ---- Bare-metal libc / libstdc++ stubs ----

    add_library(monad-zkvm-core OBJECT
        "${MONAD_ROOT}/zkvm/core/libc.cpp"
        "${MONAD_ROOT}/zkvm/core/libstdcxx.cpp"
    )
    monad_compile_options(monad-zkvm-core)
    monad_riscv_compile_options(monad-zkvm-core)

    # ---- category/core subset ----
    # zkVM-compatible mirror of the host's monad_core. The host target is
    # heavy (Boost::context, stacktrace, fiber, event ring, Linux I/O) and
    # can't add_subdirectory cleanly on RISC-V, so we build an OBJECT lib
    # with just the symbols the guest actually links against. The host's
    # assert.c (POSIX write / strlcpy / stack-backtrace) is replaced by
    # the macro substitution in zkvm/category/core/assert.h — every
    # assertion call site expands to zkvm_halt(1) inline, so no separate
    # TU is needed.
    add_library(monad-core OBJECT
        "${MONAD_ROOT}/category/core/hex.cpp"
        "${MONAD_ROOT}/category/core/rlp/decode_error.cpp"
        "${MONAD_ROOT}/category/core/checked_math.cpp"
        "${MONAD_ROOT}/category/core/seeded_fast_hash.cpp"
    )
    monad_compile_options(monad-core)
    monad_riscv_compile_options(monad-core)
    target_link_libraries(monad-core PUBLIC evmc komihash)
    # decode_error.cpp pulls boost/outcome/experimental/status-code/...
    target_compile_options(monad-core PUBLIC "-idirafter${_boost_inc}")

    # ---- category/execution (host-defined targets, adapted for zkVM here) ----
    # category/execution/CMakeLists.txt is zkVM-unaware: it defines the
    # monad_execution_{ethereum,native} OBJECT libs with the full host source
    # list and host link deps. We adapt them for the bare-metal guest — drop
    # host-only sources, drop host-only link libraries (whose targets don't
    # exist in this project), add the reduced guest deps, and apply
    # monad_riscv_compile_options. The host link list is the single source of
    # truth; the drop/add lists below mirror it (as monad_zkvm_drop_sources
    # already does for the file list).
    add_subdirectory("${MONAD_ROOT}/category/execution" execution)

    # Host-only sources: fiber dispatch, async storage, live-DB initializers,
    # event ring, full host execute_block, host precompiles/tracing paths.
    monad_zkvm_drop_sources(monad_execution_ethereum
        "dispatch_transaction.cpp"
        "execute_block.cpp"
        "validate_block.cpp"
        "block_db.cpp"
        "block_hash_buffer/util.cpp"
        "db_snapshot.cpp"
        "db_snapshot_filesystem.cpp"
        "file_db.cpp"
        "trie_db.cpp"
        "db/util.cpp"
        "db/commit_builder.cpp"
        "ecrecover.cpp"
        "exec_event_ctypes_metadata.c"
        "exec_event_recorder.cpp"
        "record_block_events.cpp"
        "record_consensus_events.cpp"
        "record_txn_events.cpp"
        "trace/event_trace.cpp"
        "trace/call_frame.cpp"
        "trace/call_tracer.cpp"
        "trace/state_tracer.cpp"
        "trace/rlp/call_frame_rlp.cpp"
        "genesis_state.cpp"
        "hive_net.cpp"
    )
    # Host-only link deps — their targets don't exist (or aren't wanted) in
    # the bare-metal guest. The shared deps (evmc, immer, unordered_dense,
    # blst, nlohmann_json) are inherited as-is. monad_crypto (vendored
    # sha256/rmd160) is dropped — the guest only needs its headers, added
    # separately if/when a surviving TU actually calls those symbols.
    monad_zkvm_drop_libraries(monad_execution_ethereum
        monad-vm
        monad_core
        monad_crypto
        monad_trie
        Boost::fiber
        Boost::json
        c-kzg-4844
        PkgConfig::brotli
        PkgConfig::crypto++
        PkgConfig::secp256k1
        intx::intx
        quill::quill
        silkpre
        TBB::tbb)

    # zkVM replacement for ecrecover.cpp — routes through zkvm_secp256k1_ecrecover.
    target_sources(monad_execution_ethereum PRIVATE
        "${MONAD_ROOT}/zkvm/category/execution/ethereum/core/ecrecover.cpp"
    )

    # validate_block.cpp is dropped (fiber dispatch, live-DB validation), but
    # the guest still references the BlockError status-code domain
    # (execute_block_zkvm / ffi.cpp return BlockError values). Provide just the
    # value_mappings() definition that backs it.
    target_sources(monad_execution_ethereum PRIVATE
        "${MONAD_ROOT}/zkvm/category/execution/ethereum/validate_block.cpp"
    )

    # Reduced guest deps not present in the inherited host link list.
    target_link_libraries(monad_execution_ethereum
        PUBLIC komihash
        PUBLIC cthash
        PUBLIC monad-vm-evm
        PUBLIC monad-vm-runtime
        PUBLIC monad-vm-interpreter)
    monad_riscv_compile_options(monad_execution_ethereum)
    target_compile_options(monad_execution_ethereum
        PUBLIC "-idirafter${_boost_inc}")
    # Vendored sha256/rmd160 headers (declarations only; e.g.
    # process_requests.cpp) — symbols resolved at final link by the Rust
    # runtime.
    target_include_directories(monad_execution_ethereum
        PUBLIC "${THIRD_PARTY_DIR}/silkpre_vendor/src")

    # monad_precompiles (extracted by the precompiles refactor) gets the same
    # host-target adaptation as monad_execution_ethereum: drop the BLS12 source
    # and host-only link deps, add the reduced guest deps, apply
    # monad_riscv_compile_options. Its objects are pulled into the guest
    # archive below (the EXPLICIT_TRAITS instantiations in precompiles.cpp are
    # needed at link).
    monad_zkvm_drop_sources(monad_precompiles
        "precompiles_bls12.cpp")

    # zkVM shadow for precompiles_bls12.cpp — provides just the msm_discount
    # gas tables reached from precompiles_gas_cost_impl.cpp; the blst-backed
    # execute paths stay out of the guest.
    target_sources(monad_precompiles PRIVATE
        "${MONAD_ROOT}/zkvm/category/execution/ethereum/precompiles_bls12.cpp"
    )

    monad_zkvm_drop_libraries(monad_precompiles
        monad-vm
        monad_core
        monad_crypto
        c-kzg-4844
        ethash::keccak
        PkgConfig::crypto++
        intx::intx
        silkpre)
    target_link_libraries(monad_precompiles
        PUBLIC komihash
        PUBLIC cthash
        PUBLIC monad-vm-evm
        PUBLIC monad-vm-runtime
        PUBLIC monad-vm-interpreter)
    # Vendored sha256/rmd160 headers (declarations only) — the symbols are
    # resolved at final link by the backend's Rust runtime.
    target_include_directories(monad_precompiles
        PUBLIC "${THIRD_PARTY_DIR}/silkpre_vendor/src")
    monad_riscv_compile_options(monad_precompiles)
    target_compile_options(monad_precompiles
        PUBLIC "-idirafter${_boost_inc}")

    # Host-only sources in monad_execution_native: fuzzer/test harnesses,
    # libsecp256k1, fiber dispatch, event-ring recorder, disk-page storage,
    # live-database commit.
    monad_zkvm_drop_sources(monad_execution_native
        "db/storage_page.cpp"
        "db/page_commit_builder.cpp"
        "db/commit_block_migration.cpp"
        "staking/fuzzer/staking_contract_machine.cpp"
        "staking/fuzzer/staking_contract_model.cpp"
        "staking/test/input_generation.cpp"
        "staking/util/secp256k1.cpp"
        "staking/staking_contract.cpp"
        "staking/read_valset.cpp"
        "dispatch_transaction.cpp"
        "execute_system_transaction.cpp"
        "event/record_consensus_events.cpp"
    )
    monad_zkvm_drop_libraries(monad_execution_native
        monad_core
        monad_crypto
        monad_trie
        evmc
        magic_enum::magic_enum
        PkgConfig::secp256k1
        quill::quill)
    monad_riscv_compile_options(monad_execution_native)

    # ---- Final guest static archive ----

    # TODO: replace the loose `category/...` source listings below with
    # add_subdirectory(...) of properly-scoped sibling libraries (e.g.
    # monad_execution_ethereum_zkvm, monad_core_zkvm) that drop the host-
    # only sources and apply monad_riscv_compile_options, mirroring how
    # monad-vm-{evm,runtime,interpreter} are pulled in above as
    # $<TARGET_OBJECTS:...>. Listing individual .cpp files here is a Phase
    # 2/3 stopgap; Phase 5 of the plan factors them into the proper
    # cross-compile libraries.
    add_library(${_guest_target} STATIC
        "${CMAKE_CURRENT_SOURCE_DIR}/ffi.cpp"
        "${CMAKE_CURRENT_SOURCE_DIR}/execute_block_zkvm.cpp"
        "${CMAKE_CURRENT_SOURCE_DIR}/body_roots.cpp"
        # Precompile golden-vector test entry (monad_zkvm_run_precompile_tests).
        # Pulled into the archive so a test binary can link it; dead-stripped
        # from the witness binary, which references only the witness entry.
        "${CMAKE_CURRENT_SOURCE_DIR}/../test/precompile_tests/precompile_test.cpp"
        "${MONAD_ROOT}/category/vm/memory_pool.cpp"
        $<TARGET_OBJECTS:monad-core>
        $<TARGET_OBJECTS:monad-zkvm-core>
        $<TARGET_OBJECTS:monad_precompiles>
        $<TARGET_OBJECTS:monad_execution_ethereum>
        $<TARGET_OBJECTS:monad_execution_native>
        $<TARGET_OBJECTS:monad-vm-evm>
        $<TARGET_OBJECTS:monad-vm-runtime>
        $<TARGET_OBJECTS:monad-vm-interpreter>
        ${_libc_objs}
        ${_libgcc_objs}
    )
    monad_compile_options(${_guest_target})
    monad_riscv_compile_options(${_guest_target})
    target_link_libraries(${_guest_target}
        PUBLIC evmc unordered_dense komihash immer
        nlohmann_json::nlohmann_json)
    target_compile_options(${_guest_target}
        PUBLIC "-idirafter${_boost_inc}")

else()
    # ---- Host x86 mode ----
    # Reached via add_subdirectory(zkvm/guest) from the root host CMakeLists.
    # x86 has a single consumer (monad-zkvm-x86-test-runner), so ffi.cpp +
    # x86_test_runner.cpp compile straight into the executable; no
    # intermediate static library.

    add_executable(monad-zkvm-x86-test-runner
        "${CMAKE_CURRENT_SOURCE_DIR}/ffi.cpp"
        "${CMAKE_CURRENT_SOURCE_DIR}/execute_block_zkvm.cpp"
        "${CMAKE_CURRENT_SOURCE_DIR}/body_roots.cpp"
        "${CMAKE_CURRENT_SOURCE_DIR}/x86_test_runner.cpp"
    )
    monad_compile_options(monad-zkvm-x86-test-runner)
    target_link_libraries(monad-zkvm-x86-test-runner PRIVATE monad_execution)

    # Precompile golden-vector test runner: same x86 driver, but its entry is
    # the precompile-vector harness instead of the witness executor.
    add_executable(monad-zkvm-x86-precompile-test
        "${CMAKE_CURRENT_SOURCE_DIR}/../test/precompile_tests/precompile_test.cpp"
        "${CMAKE_CURRENT_SOURCE_DIR}/x86_test_runner.cpp"
    )
    monad_compile_options(monad-zkvm-x86-precompile-test)
    target_compile_definitions(monad-zkvm-x86-precompile-test PRIVATE
        MONAD_ZKVM_X86_ENTRY=monad_zkvm_run_precompile_tests)
    target_link_libraries(monad-zkvm-x86-precompile-test PRIVATE monad_execution)

endif()
