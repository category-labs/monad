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

# The monad zkVM guest library. The guest sources proper live in the
# monad-zkvm-guest OBJECT library, defined once at the bottom of this file
# and consumed by both modes:
#
# 1. Cross-compile (RISC-V): invoked standalone as the top-level CMake
#    project (via `cmake -S zkvm/guest ...`, typically from the build-support
#    crate). The caller sets MONAD_ZKVM_GUEST_TARGET to a backend suffix
#    (zisk or sp1) — used only to name the resulting archive
#    (monad-zkvm-guest-<suffix>). This file drives the full bare-metal
#    build and bundles everything, monad-zkvm-guest included, into a single
#    STATIC archive.
#
# 2. Host x86: invoked from the root host CMakeLists.txt via
#    add_subdirectory(zkvm/guest). MONAD_ZKVM_GUEST_TARGET is not set;
#    this file builds the monad-zkvm-x86-test-runner executable from
#    x86_test_runner.cpp + monad-zkvm-guest, linked against the host's
#    existing monad_execution target.

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

    # Lever: L2 semantics -- encrypted transactions, the end-of-block message
    # anchor, no gas economics. A MODE and not an optimisation, so it is
    # declared here AND at root scope (see cmake/l2.cmake for the ODR reason);
    # this branch is a standalone project and sees none of the root's options.
    #
    # A witness built for one setting is rejected outright by the other -- six
    # RLP fields against seven, InputTooShort one way and InputTooLong the
    # other -- which is why the envelope needs no version byte.
    option(MONAD_ZKVM_L2
           "L2 semantics: encrypted transactions, message anchor, no gas economics"
           OFF)
    if(MONAD_ZKVM_L2)
        # Relative: MONAD_ROOT is not set until much further down this file.
        include("${CMAKE_CURRENT_SOURCE_DIR}/../../cmake/l2.cmake")
        monad_l2_compile_definitions()
        if(NOT MONAD_ZKVM_GUEST_TARGET STREQUAL "zisk")
            message(FATAL_ERROR
                "MONAD_ZKVM_L2 needs ZisK: the ECDH rides zisklib's "
                "secp256k1_add/_dbl precompiles and Poseidon2 rides csrs 0x812, "
                "and SP1 has neither. A software curve would measure the "
                "software curve, not this protocol.")
        endif()
        # The three public values fill 96 bytes, the anchor and the block
        # number take it to 136, and the keccak-site tail is 2 * 19 * 4 = 152 --
        # so 136 + 152 = 288 against ZisK's 256-byte committed output. The
        # diagnostic build on its own already sits at 96 + 152 = 248.
        if(MONAD_ZKVM_KECCAK_SITES)
            message(FATAL_ERROR
                "MONAD_ZKVM_L2 and MONAD_ZKVM_KECCAK_SITES together need 296 "
                "bytes of public output against ZisK's 256-byte cap")
        endif()
    endif()

    # Build-dependent optimisations must extend both the feature list and
    # post-link audit. Source-only changes need no feature bit: the commit
    # and ELF hash already identify them.
    option(MONAD_ZKVM_OFFICIAL_PROFILE
           "build the audited, fail-closed official ZisK guest profile" OFF)
    set(_monad_zkvm_official_features "baseline" "zisk-dma" "keccakf-memo"
                                      "wide-memory-size" "varcode-cache"
                                      "no-dirty-accounts"
                                      "no-merge-constraints"
                                      "jumpdest-precompile")
    set(_monad_zkvm_runtime_version "1.3.1-alpha")
    set(_monad_zkvm_runtime_revision
        "306a9c934ba4947b1d586d69b67120f8b4c41466")
    if(MONAD_ZKVM_OFFICIAL_PROFILE AND
       NOT MONAD_ZKVM_GUEST_TARGET STREQUAL "zisk")
        message(FATAL_ERROR
            "MONAD_ZKVM_OFFICIAL_PROFILE is a ZisK-only build profile")
    endif()

    # Enable options required by the official profile; reject explicit OFF values.
    # Add each new required option here and its feature to the list above.
    # NO_DIRTY_ACCOUNTS and NO_MERGE_CONSTRAINTS both remove work whose only
    # readers are outside the guest -- the state tracer this file excludes, and
    # the can_merge the sequential path does not call.
    set(_monad_zkvm_required_levers MONAD_ZKVM_ZISK_DMA
                                    MONAD_ZKVM_KECCAKF_MEMO
                                    MONAD_ZKVM_WIDE_MEMORY_SIZE
                                    MONAD_ZKVM_VARCODE_CACHE
                                    MONAD_ZKVM_NO_DIRTY_ACCOUNTS
                                    MONAD_ZKVM_NO_MERGE_CONSTRAINTS)
    if(MONAD_ZKVM_OFFICIAL_PROFILE)
        # Audit the effective source list and per-source definitions.
        set(CMAKE_EXPORT_COMPILE_COMMANDS ON CACHE BOOL
            "required by the official build audit" FORCE)
        foreach(_lever ${_monad_zkvm_required_levers})
            if(DEFINED ${_lever} AND NOT ${_lever})
                message(FATAL_ERROR
                    "${_lever}=OFF contradicts MONAD_ZKVM_OFFICIAL_PROFILE=ON: "
                    "this lever is required by the official feature set. "
                    "For an ablation, disable the official profile and "
                    "configure the other levers explicitly.")
            endif()
            set(${_lever} ON CACHE BOOL
                "required by the official ZisK profile" FORCE)
        endforeach()
    endif()

    # The official profile signs one binary. The assertion below is extra work
    # on the merge path and aborts where the shipped guest returns, so a build
    # carrying it is not the guest the signature describes. Forbidding it here
    # is also what keeps it from colliding with the NO_MERGE_CONSTRAINTS forced
    # on just above, whose writes that assertion's can_merge would read.
    if(MONAD_ZKVM_OFFICIAL_PROFILE AND MONAD_ZKVM_CHECK_SEQUENTIAL_MERGE)
        message(FATAL_ERROR
            "MONAD_ZKVM_CHECK_SEQUENTIAL_MERGE is forbidden in the official "
            "ZisK profile")
    endif()

    # The official artifact is the L1 mainnet prover. The feature list and the
    # ELF marker encode a FEATURE SET; L2 is a different RULE SET, and one
    # signature must not be able to cover both. An audited L2 profile, if it
    # is ever wanted, is a second profile with its own marker.
    if(MONAD_ZKVM_OFFICIAL_PROFILE AND MONAD_ZKVM_L2)
        message(FATAL_ERROR
            "MONAD_ZKVM_L2 changes the witness shape and the consensus rules; "
            "the official profile must not claim one identity for two")
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

    # ZisK supports Zbb/Zbs/Zbkb since v1.2.0-alpha.
    # The fixed-address guest needs no PIC/GOT indirections.
    #
    # Append after cmake-rs's flags: the last -march wins.
    if(MONAD_ZKVM_GUEST_TARGET STREQUAL "zisk")
        set(_zisk_march "-march=rv64ima_zicsr_zbb_zbs_zbkb -mabi=lp64")
        string(APPEND CMAKE_C_FLAGS " ${_zisk_march} -fno-pic")
        string(APPEND CMAKE_CXX_FLAGS " ${_zisk_march} -fno-pic")
        string(APPEND CMAKE_ASM_FLAGS " ${_zisk_march}")
    endif()

    # Tune C++ inlining for both guests to reduce call overhead.
    # Allow more overall growth while limiting individual inlining candidates.
    # Unroll eligible loops to reduce comparisons and branches.
    # Keep these options in CMAKE_CXX_FLAGS so the official profile hashes them.
    string(APPEND CMAKE_CXX_FLAGS
        " --param inline-unit-growth=800"
        " --param large-function-growth=1500"
        " --param max-inline-insns-auto=200"
        " --param max-inline-insns-single=800"
        " --param inline-min-speedup=1"
        " -finline-functions"
        " -funroll-loops")

    set(_guest_target "monad-zkvm-guest-${MONAD_ZKVM_GUEST_TARGET}")

    # Lever: Memory::size and ::capacity are uint32_t, and every memory-touching opcode reads
    # size. ZisK charges a 4-byte read 122 cells against 17 for an aligned 8-byte one, and makes
    # `*offset + 32` an add_w at 60 rather than a native add at 15.3.
    #
    # Declared only here, and only in this branch, because the layout is the guest's alone: the
    # native x86 compiler emits a 32-bit read of the field at a fixed offset and context.S
    # addresses the same offsets by hand. The guest drops every .S and never builds that emitter.
    # types.hpp turns a leak into a build failure rather than a silent half-word read.
    option(MONAD_ZKVM_WIDE_MEMORY_SIZE
           "64-bit Memory::size and ::capacity, which x86 cannot take" OFF)
    if(MONAD_ZKVM_WIDE_MEMORY_SIZE)
        add_compile_definitions(MONAD_ZKVM_WIDE_MEMORY_SIZE)
    endif()

    # Lever: give the guest's VM shadow the varcode cache the host has. The
    # shadow's find_varcode finds nothing without it, so every read of an
    # existing contract rebuilds a Varcode and its control block out of an
    # intercode BlockState::code_ already holds. Nothing is re-decoded.
    option(MONAD_ZKVM_VARCODE_CACHE
           "cache varcodes by code hash in the guest's VM shadow" OFF)
    if(MONAD_ZKVM_VARCODE_CACHE)
        add_compile_definitions(MONAD_ZKVM_VARCODE_CACHE)
    endif()

    # Omit dirty-account tracking when neither tracing nor reserve-balance
    # tracking needs it. State rejects active reserve tracking in this mode.
    option(MONAD_ZKVM_NO_DIRTY_ACCOUNTS
           "omit dirty-account lists and forbid consumers that require them" OFF)
    if(MONAD_ZKVM_NO_DIRTY_ACCOUNTS)
        add_compile_definitions(MONAD_ZKVM_NO_DIRTY_ACCOUNTS)
    endif()

    # Diagnostic: the guest's per-tx loop is serialized, so it runs transactions through
    # ExecuteTransaction::execute(SequentialExecutionToken), which skips the merge-conflict check
    # the node's speculative scheduler needs. This restores that check as an assertion on the
    # same path, in the same place, so a corpus run either upholds the token's claim or aborts.
    # The differential arm for any change to the guest's scheduling; forbidden in the official
    # profile alongside the other diagnostics.
    option(MONAD_ZKVM_CHECK_SEQUENTIAL_MERGE
           "assert can_merge on the sequential merge path" OFF)
    if(MONAD_ZKVM_CHECK_SEQUENTIAL_MERGE)
        add_compile_definitions(MONAD_ZKVM_CHECK_SEQUENTIAL_MERGE)
    endif()

    # Skip merge constraints in the sequential guest; the host keeps them.
    # Incompatible with CHECK_SEQUENTIAL_MERGE, which reads those constraints.
    option(MONAD_ZKVM_NO_MERGE_CONSTRAINTS
           "stop writing the merge constraints only can_merge reads" OFF)
    if(MONAD_ZKVM_NO_MERGE_CONSTRAINTS)
        if(MONAD_ZKVM_CHECK_SEQUENTIAL_MERGE)
            message(FATAL_ERROR
                "MONAD_ZKVM_NO_MERGE_CONSTRAINTS removes what CHECK_SEQUENTIAL_MERGE's assertion "
                "reads; enabling both would fail the assertion for the wrong reason")
        endif()
        add_compile_definitions(MONAD_ZKVM_NO_MERGE_CONSTRAINTS)
    endif()

    # Expose the backend as a compile definition, for the places where the two
    # diverge: the ripemd160 accelerators place the digest at opposite ends of
    # their 32-byte output word, so the precompile shim normalises them
    # differently (zkvm/category/execution/ethereum/precompiles_impl.hpp), and
    # the Keccak-f[1600] precompile is reached by a different entry on each
    # (zkvm/guest/keccak_accel.cpp).

    # Diagnostic counters after the 32-byte block hash; disabled by default.
    # Layout: little-endian u32 call counts, then permutation counts,
    # in the site order defined by zkvm/category/core/keccak_sites.hpp.
    option(MONAD_ZKVM_KECCAK_SITES "count keccak calls per call site" OFF)
    if(MONAD_ZKVM_KECCAK_SITES)
        add_compile_definitions(MONAD_ZKVM_KECCAK_SITES)
    endif()

    if(MONAD_ZKVM_GUEST_TARGET STREQUAL "sp1")
        add_compile_definitions(MONAD_ZKVM_SP1)
    elseif(MONAD_ZKVM_GUEST_TARGET STREQUAL "zisk")
        add_compile_definitions(MONAD_ZKVM_ZISK)

        # Memoise Keccak-f through ZisK's executor-side index (fcall 24/25),
        # zkvm/guest/keccak_accel.cpp. ~14 % of a block's permutations repeat
        # a state, and the lookup costs the guest nothing the cost model
        # charges for. OFF compiles the mechanism out — table, fcalls and
        # branch — so it is a control arm and not a disabled predicate:
        #   -DMONAD_ZKVM_KECCAKF_MEMO=OFF
        # It costs 100 MiB of .bss, which is why it is a switch at all.
        option(MONAD_ZKVM_KECCAKF_MEMO "memoise Keccak-f via the ZisK executor index" ON)
        if(NOT MONAD_ZKVM_KECCAKF_MEMO)
            add_compile_definitions(MONAD_ZKVM_KECCAKF_MEMO=0)
        endif()
        # Favor direct unaligned word accesses on ZisK over byte-wise loads.
        # SP1's handling of unaligned accesses has not been validated here.
        # Set tuning before the official profile hashes the compiler flags.
        string(APPEND CMAKE_C_FLAGS " -mtune=generic-ooo")
        string(APPEND CMAKE_CXX_FLAGS " -mtune=generic-ooo")

        # Expose the no-op operator delete declarations to every ZisK C++ file.
        string(APPEND CMAKE_CXX_FLAGS
               " -include ${CMAKE_CURRENT_SOURCE_DIR}/nodelete.hpp")

        # Lower eligible block memory operations, including struct copies,
        # directly to ZisK DMA. Requires Zicsr and the patched compiler built by
        # zkvm/toolchain/zisk-dma-gcc/build-gcc15.sh.
        # The official profile also probes the emitted code for a DMA marker.
        option(MONAD_ZKVM_ZISK_DMA
               "lower block mem* to the ZisK DMA precompile" OFF)
        if(MONAD_ZKVM_ZISK_DMA)
            string(APPEND CMAKE_C_FLAGS " -mzisk-dma")
            string(APPEND CMAKE_CXX_FLAGS " -mzisk-dma")
            # Tells the keccak memo that a constant-size block move reaches the
            # port INLINE here, so it should stop hiding the length from the
            # optimiser to force an out-of-line call. Worth 20.2 M COST a block.
            # Defined by the same branch that adds the flag: a source-side guess
            # about which compiler is in use is exactly what would drift.
            add_compile_definitions(MONAD_ZKVM_ZISK_DMA_LOWERING)
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

        # When DMA is requested, verify emitted code, not just flag acceptance.
        # A compiler hash identifies the binary but does not prove DMA support.
        if(CMAKE_CXX_FLAGS MATCHES "-mzisk-dma" OR CMAKE_C_FLAGS MATCHES "-mzisk-dma")
            # Use the guest's C flags, including Zicsr. sink exposes the copied
            # bytes to an external call.
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
    if(MONAD_ZKVM_GUEST_TARGET STREQUAL "zisk")
        add_compile_definitions(MONAD_ZKVM_ZISK)
        # Also enables the interpreter's dispatch table argument (types.hpp).
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

    # Avoid soft-float calls with a guest-only header using integer load-factor
    # arithmetic. Leave the unordered_dense submodule unchanged.
    include("${CMAKE_CURRENT_SOURCE_DIR}/unordered_dense_derive.cmake")
    monad_zkvm_unordered_dense_derive(unordered_dense "${THIRD_PARTY_DIR}"
        "${CMAKE_CURRENT_BINARY_DIR}/unordered_dense-nofloat")

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

    # The interpreter-only slice of the host's monad-vm target. The zkVM
    # shadow of vm.hpp still owns a MemoryPool, so its out-of-line definitions
    # are needed, but the rest of monad-vm (compiler.cpp, varcode_cache.cpp,
    # vm.cpp) pulls in asmjit, TBB and quill and stays out of the guest.
    add_library(monad-vm-mempool OBJECT
        "${MONAD_ROOT}/category/vm/memory_pool.cpp")
    monad_compile_options(monad-vm-mempool)
    monad_riscv_compile_options(monad-vm-mempool)

    # ---- Extract setjmp/longjmp from the compiler's newlib libc.a ----

    # Match the guest's -march/-mabi when selecting multilib libraries.
    # The compiler default may otherwise select incompatible RV32 objects.
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
    # the symbol lives in _popcountsi2.o because libgcc names units
    # by word count (SI = single word = historically 32 bits)
    # and symbols by machine mode si = 32, di = 64, ti = 128 bits
    # where risvc64 word is 64 bits, hence __popcount*di*2
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

    # Compute the build identity after all guest flags are set.
    # Add new flags above this block so the signature includes them.
    if(MONAD_ZKVM_OFFICIAL_PROFILE)
        file(SHA256 "${CMAKE_CXX_COMPILER}" _official_cxx_sha256)
        # Hash the patch set separately from host-dependent compiler binaries.
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
        # Normalise the guest source path (e.g. in -include nodelete.hpp) so
        # build signatures do not depend on the checkout location.
        # Compilation still uses the original flags and paths.
        set(_official_signed_inputs
            "${_official_cxx_sha256}\n${CMAKE_C_FLAGS}\n${CMAKE_C_FLAGS_RELEASE}\n${CMAKE_CXX_FLAGS}\n${CMAKE_CXX_FLAGS_RELEASE}\n${CMAKE_ASM_FLAGS}\n${CMAKE_ASM_FLAGS_RELEASE}\n${_monad_zkvm_runtime_revision}\n${_official_features_csv}\n${_dma_patch_sha}")
        string(REPLACE "${CMAKE_CURRENT_SOURCE_DIR}" "<guest>"
               _official_signed_inputs "${_official_signed_inputs}")
        string(SHA256 _official_build_signature "${_official_signed_inputs}")
        # Keep the feature switch global, but attach build identity only to
        # execute_witness.cpp, its sole reader. A new commit then recompiles
        # that file without invalidating every object.
        add_compile_definitions(MONAD_ZKVM_OFFICIAL_PROFILE=1)
        set(_monad_zkvm_stamp_defs
            "MONAD_ZKVM_BUILD_COMMIT=\"${MONAD_ZKVM_GIT_COMMIT}\""
            "MONAD_ZKVM_BUILD_SIGNATURE=\"${_official_build_signature}\""
            "MONAD_ZKVM_BUILD_FEATURES=\"${_official_features_csv}\""
            "MONAD_ZKVM_RUNTIME_VERSION=\"${_monad_zkvm_runtime_version}\"")
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
        # Mark development builds explicitly in both the ELF and JSON profile.
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
        # Poseidon2-16 over Goldilocks. One source serves both sides: the
        # sponge is shared and only the permutation switches, native on the
        # host and csrs 0x812 here, so a witness generator and the guest
        # compute the same digest by construction rather than by agreement.
        "${MONAD_ROOT}/category/core/poseidon2.cpp"
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
        "block_db.cpp"
        "block_hash_buffer/util.cpp"
        "db_snapshot.cpp"
        "db_snapshot_filesystem.cpp"
        "file_db.cpp"
        "trie_db.cpp"
        "db/util.cpp"
        "db/commit_builder.cpp"
        # The witness generator. Nothing in the guest produces a blob, and
        # leaving it out keeps the guest's archive -- and so the official
        # profile's ELF -- what it was before this file existed.
        "db/witness_generator.cpp"
        "ecrecover/impl.cpp"
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

    # validate_block.cpp carries the validators and the BlockError
    # value_mappings() the shadow used to provide alone.

    # Only the official profile supplies these build stamps.
    if(_monad_zkvm_stamp_defs)
        set_source_files_properties("${CMAKE_CURRENT_SOURCE_DIR}/execute_witness.cpp"
            PROPERTIES COMPILE_DEFINITIONS "${_monad_zkvm_stamp_defs}")
    endif()

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
    # Revert-semantics self-test. In the archive like the precompile golden vectors above, so a
    # binary can link it and the witness binary dead-strips it. With MONAD_ZKVM_SELFTEST=ON the
    # witness entry calls it instead of reading a witness, which is what lets it run under ziskemu
    # on a machine where the node's host build cannot: that build requires __AVX2__.
    option(MONAD_ZKVM_SELFTEST "guest entry runs the state self-test instead of a witness" OFF)
    if(MONAD_ZKVM_SELFTEST)
        add_compile_definitions(MONAD_ZKVM_SELFTEST)
    endif()

    # Compiled ONLY under the option. Measured: adding it to the archive unconditionally changed
    # the witness binary's sha -- its static globals and the stub's vtable survive --gc-sections --
    # so "in the archive, dead-stripped from the witness binary" does not hold for this file.
    set(_selftest_sources "")
    if(MONAD_ZKVM_SELFTEST)
        set(_selftest_sources
            "${CMAKE_CURRENT_SOURCE_DIR}/../../category/execution/ethereum/state3/test/revert_semantics_test.cpp")
    endif()

    # Compiled ONLY under the option, on the same measured grounds as
    # _selftest_sources above: monad_l2_chain.cpp has a vtable, which survives
    # --gc-sections. Gated, a non-L2 ELF stays byte for byte what it is today,
    # and that is the property the official profile's signature rests on.
    set(_l2_sources "")
    if(MONAD_ZKVM_L2)
        # Which sources a suite is made of lives in cmake/l2.cmake, next to the
        # list of suites it validates against -- see the note there on why this
        # is not spelled out in each of this file's two branches.
        monad_l2_sources("${CMAKE_CURRENT_SOURCE_DIR}" _l2_sources)
    endif()

    add_library(${_guest_target} STATIC
        ${_selftest_sources}
        $<TARGET_OBJECTS:monad-zkvm-guest>
        # Linked only by the precompile test binary.
        "${CMAKE_CURRENT_SOURCE_DIR}/../test/precompile_tests/precompile_test.cpp"
        $<TARGET_OBJECTS:monad-core>
        $<TARGET_OBJECTS:monad-zkvm-core>
        $<TARGET_OBJECTS:monad_precompiles>
        $<TARGET_OBJECTS:monad_execution_ethereum>
        $<TARGET_OBJECTS:monad_execution_native>
        $<TARGET_OBJECTS:monad-vm-evm>
        $<TARGET_OBJECTS:monad-vm-runtime>
        $<TARGET_OBJECTS:monad-vm-interpreter>
        $<TARGET_OBJECTS:monad-vm-mempool>
        ${_libc_objs}
        ${_libgcc_objs}
    )
    monad_compile_options(${_guest_target})
    monad_riscv_compile_options(${_guest_target})
    # cthash is here and not only on monad_execution_ethereum because the
    # guest's OWN sources reach it: namespace_anchor.hpp derives its topic0
    # through abi_encode_event_signature, which is consteval over cthash's
    # Keccak, and l2_config.hpp includes that header. Before this branch
    # nothing in the guest included core/contract/abi_signatures.hpp, so the
    # include path it needs was never on this target.
    target_link_libraries(${_guest_target}
        PRIVATE monad-core monad_execution_ethereum)

else()
    # ---- Host x86 mode ----
    # Reached via add_subdirectory(zkvm/guest) from the root host CMakeLists.
    # The x86 driver links the shared monad-zkvm-guest objects against the
    # host's existing monad_execution target.

    # Mirrors the cross branch's gate. The definitions themselves come from the
    # root scope, which this branch is a subdirectory of.
    set(_l2_sources "")
    if(MONAD_ZKVM_L2)
        # Which sources a suite is made of lives in cmake/l2.cmake, next to the
        # list of suites it validates against -- see the note there on why this
        # is not spelled out in each of this file's two branches.
        monad_l2_sources("${CMAKE_CURRENT_SOURCE_DIR}" _l2_sources)
    endif()

    add_executable(monad-zkvm-x86-test-runner
        "${CMAKE_CURRENT_SOURCE_DIR}/x86_test_runner.cpp"
    )
    monad_compile_options(monad-zkvm-x86-test-runner)
    target_link_libraries(monad-zkvm-x86-test-runner
        PRIVATE monad-zkvm-guest monad_execution zkevm-standards)

    # The corpus generator: builds witnesses from a genesis state rather than
    # rewriting someone else's, so the blocks obey this chain's rules instead
    # of being made to fit. See zkvm/test/corpus/corpus_builder.hpp.
    set(_corpus_sources
        "${CMAKE_CURRENT_SOURCE_DIR}/../test/corpus/tx_sign.cpp"
        "${CMAKE_CURRENT_SOURCE_DIR}/../test/corpus/genesis_bulk.cpp"
        "${CMAKE_CURRENT_SOURCE_DIR}/../test/corpus/witness_stats.cpp"
        "${CMAKE_CURRENT_SOURCE_DIR}/../test/corpus/corpus_builder.cpp"
        "${CMAKE_CURRENT_SOURCE_DIR}/../test/corpus/token_contracts.cpp"
        "${CMAKE_CURRENT_SOURCE_DIR}/../test/corpus/workload.cpp"
        "${CMAKE_CURRENT_SOURCE_DIR}/../test/corpus/scenarios.cpp")

    # In an L2 tree the generator encrypts the leaves and emits a seven-field
    # witness, so it needs the cipher sources. The ciphertext transactions root
    # needs none: ordered_trie_root is a template in db/ordered_trie.hpp. Out
    # of one, the same sources build a plaintext corpus and none of this is
    # compiled.
    set(_corpus_extra "")
    set(_corpus_libs "")
    if(MONAD_ZKVM_L2)
        monad_l2_sources("${CMAKE_CURRENT_SOURCE_DIR}" _corpus_l2)
        monad_l2_cipher_host_libs(_corpus_l2_libs)
        list(APPEND _corpus_extra ${_corpus_l2})
        list(APPEND _corpus_libs ${_corpus_l2_libs})
    endif()

    add_executable(monad-zkvm-corpus-gen
        ${_corpus_sources}
        ${_corpus_extra}
        "${CMAKE_CURRENT_SOURCE_DIR}/../test/corpus/corpus_gen_main.cpp")
    monad_compile_options(monad-zkvm-corpus-gen)
    target_link_libraries(monad-zkvm-corpus-gen PRIVATE
        monad_execution secp256k1 ${_corpus_libs})

    # secp256k1 is silkpre's vendored target, and it already reaches these
    # through monad_execution -> monad_crypto, both PUBLIC. Named anyway
    # because the signer calls it directly, and a direct caller should not
    # depend on a transitive edge it does not own.
    monad_add_test(test_corpus_builder
        ${_corpus_sources}
        ${_corpus_extra}
        "${CMAKE_CURRENT_SOURCE_DIR}/../test/corpus/test_corpus_builder.cpp")
    target_link_libraries(test_corpus_builder
        secp256k1 ${_corpus_libs})

    # The witnesses the guest must refuse. It drives the real runner as a
    # subprocess -- a bad witness is signalled by aborting, so the thing under
    # test is a process exit -- hence the dependency rather than a link.
    monad_add_test(test_witness_rejection
        ${_corpus_sources}
        ${_corpus_extra}
        "${CMAKE_CURRENT_SOURCE_DIR}/../test/corpus/test_witness_rejection.cpp")
    target_link_libraries(test_witness_rejection
        secp256k1 ${_corpus_libs})
    add_dependencies(test_witness_rejection monad-zkvm-x86-test-runner)

    # Precompile golden-vector test runner: same x86 driver, but its entry is
    # the precompile-vector harness instead of the witness executor.
    add_executable(monad-zkvm-x86-precompile-test
        "${CMAKE_CURRENT_SOURCE_DIR}/../test/precompile_tests/precompile_test.cpp"
        "${CMAKE_CURRENT_SOURCE_DIR}/x86_test_runner.cpp"
    )
    monad_compile_options(monad-zkvm-x86-precompile-test)
    target_compile_definitions(monad-zkvm-x86-precompile-test PRIVATE
        MONAD_ZKVM_X86_ENTRY=monad_zkvm_run_precompile_tests)
    target_link_libraries(monad-zkvm-x86-precompile-test
        PRIVATE monad_execution zkevm-standards)

    # ---- L2 unit tests ----
    # Registered by hand rather than by monad_add_test_folder: each one needs
    # the guest source it exercises compiled alongside it, and those sources
    # are not in monad_execution -- they are the guest's own.
    #
    # Built in a PLAIN host tree, not only under MONAD_ZKVM_L2, so the cipher
    # and the decoder are testable without a deployment's eight required
    # values. l2_cipher_suite.hpp defaults the suite for exactly this case.
    monad_l2_cipher_sources("${CMAKE_CURRENT_SOURCE_DIR}" _l2_suite_sources)
    monad_l2_cipher_host_libs(_l2_host_libs)

    monad_add_test(l2_sponge_test
        "${CMAKE_CURRENT_SOURCE_DIR}/../test/l2/l2_sponge_test.cpp"
        "${CMAKE_CURRENT_SOURCE_DIR}/l2_sponge.cpp")

    # The ECDH suite's own test, so it names that suite's source directly
    # rather than the selected one: it exists to test secp256k1 against
    # libsecp256k1, and means nothing for a suite without a curve.
    monad_add_test(l2_ecdh_test
        "${CMAKE_CURRENT_SOURCE_DIR}/../test/l2/l2_ecdh_test.cpp"
        "${CMAKE_CURRENT_SOURCE_DIR}/l2_ecdh.cpp")
    target_link_libraries(l2_ecdh_test secp256k1)

    monad_add_test(l2_cipher_test
        "${CMAKE_CURRENT_SOURCE_DIR}/../test/l2/l2_cipher_test.cpp"
        "${CMAKE_CURRENT_SOURCE_DIR}/l2_sponge.cpp"
        ${_l2_suite_sources})
    target_link_libraries(l2_cipher_test ${_l2_host_libs})

    monad_add_test(decode_block_l2_test
        "${CMAKE_CURRENT_SOURCE_DIR}/../test/l2/decode_block_l2_test.cpp"
        "${CMAKE_CURRENT_SOURCE_DIR}/decode_block_l2.cpp"
        "${CMAKE_CURRENT_SOURCE_DIR}/l2_sponge.cpp"
        ${_l2_suite_sources})
    target_link_libraries(decode_block_l2_test ${_l2_host_libs})

endif()

# ---- Guest sources, shared by both modes ----
# The witness pipeline itself. Defined once, after the mode split: the two
# modes differ only in what these sources compile against — the adapted
# bare-metal targets on RISC-V, the host's monad_execution on x86 — so only
# the dependency edge is conditional, never the target or its file list.
# The cipher, the sponge, the L2 chain and the ciphertext block decoder. Here
# and not in either mode's own target, for the reason the paragraph above
# gives: the two modes differ in what these compile AGAINST, never in which
# files they are.
set(_l2_sources "")
if(MONAD_ZKVM_L2)
    monad_l2_sources("${CMAKE_CURRENT_SOURCE_DIR}" _l2_sources)
endif()

add_library(monad-zkvm-guest OBJECT
    ${_l2_sources}
    "${CMAKE_CURRENT_SOURCE_DIR}/keccak_accel.cpp"
    "${CMAKE_CURRENT_SOURCE_DIR}/execute_block.cpp"
    "${CMAKE_CURRENT_SOURCE_DIR}/execute_witness.cpp"
    "${CMAKE_CURRENT_SOURCE_DIR}/witness_block_hash_buffer.cpp"
)
monad_compile_options(monad-zkvm-guest)
target_link_libraries(monad-zkvm-guest PRIVATE zkevm-standards)
if(DEFINED MONAD_ZKVM_GUEST_TARGET)
    monad_riscv_compile_options(monad-zkvm-guest)
    target_link_libraries(monad-zkvm-guest
        PRIVATE monad-core monad_execution_ethereum)
else()
    target_link_libraries(monad-zkvm-guest PRIVATE monad_execution)
    if(MONAD_ZKVM_L2)
        # Whatever the selected suite's host arm needs; see cmake/l2.cmake.
        # PUBLIC so every binary that links these objects gets the curve.
        monad_l2_cipher_host_libs(_l2_host_libs)
        target_link_libraries(monad-zkvm-guest PUBLIC ${_l2_host_libs})
    endif()
endif()

# ---- eth-act zkEVM standards (header-only), shared by both modes ----
# The vendored zkevm-standards submodule: io-interface/zkvm_io.h (the guest's
# read_input / write_output ABI) and c-interface-accelerators/
# zkvm_accelerators.h (the crypto accelerator ABI the RISC-V shadows call).
# Targets take it as a link dependency rather than adding the include dir
# by hand; monad_riscv_compile_options links it for every bare-metal target.
add_library(zkevm-standards INTERFACE)
target_include_directories(zkevm-standards
    INTERFACE "${THIRD_PARTY_DIR}/zkevm-standards/standards")
