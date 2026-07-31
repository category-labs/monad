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

    if(NOT MONAD_ZKVM_GUEST_TARGET MATCHES "^(zisk|sp1|openvm)$")
        message(FATAL_ERROR
            "MONAD_ZKVM_GUEST_TARGET must be 'zisk', 'sp1' or 'openvm', got "
            "'${MONAD_ZKVM_GUEST_TARGET}'")
    endif()
    if(MONAD_COMPILER_TESTING)
        message(FATAL_ERROR
            "MONAD_COMPILER_TESTING is not supported in zkVM builds")
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

    # OpenVM only: no switch jump tables. GCC emits those as a rodata word per
    # case holding `case_target - table_base`, which on RISC-V is an
    # R_RISCV_ADD32/R_RISCV_SUB32 relocation pair. powdr's ELF reader — which
    # the autoprecompile pipeline goes through to recover basic-block
    # boundaries — accepts only R_RISCV_32 in data sections and panics on
    # anything else. A Rust guest never produces label-difference pairs, so
    # upstream has not needed to handle them; this C++ guest produced 395.
    # The cost is comparison chains in place of an indirect jump for large
    # switches, which is why it is scoped to the one backend that needs it.
    if(MONAD_ZKVM_GUEST_TARGET STREQUAL "openvm")
        string(APPEND CMAKE_C_FLAGS " -fno-jump-tables")
        string(APPEND CMAKE_CXX_FLAGS " -fno-jump-tables")
    endif()

    set(_guest_target "monad-zkvm-guest-${MONAD_ZKVM_GUEST_TARGET}")

    # The SP1 and ZisK ripemd160 accelerators place the digest at opposite
    # ends of their 32-byte output word, so the precompile shim normalises
    # them differently (zkvm/category/execution/ethereum/precompiles_impl.hpp).
    # Expose the backend as a compile definition for that per-backend branch.
    # OpenVM needs none: its shims (zkvm/openvm/src/accel.rs) follow the ZisK
    # conventions — digest at [12,32), EIP-2537 point encodings — so the
    # unbranched path is already correct for it.
    if(MONAD_ZKVM_GUEST_TARGET STREQUAL "sp1")
        add_compile_definitions(MONAD_ZKVM_SP1)
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

    # ---- immer portability patch (upstream bug, 32-bit targets only) ----
    #
    # immer v0.8.1's node::sizeof_values_n calls
    #     std::max(sizeof(values_t), immer_offsetof(...) + sizeof(...) * count)
    # whose arguments are size_t and count_t (= uint32_t). On a 64-bit target
    # the product promotes to size_t and both arguments agree, so the call
    # compiles. On rv32 with this newlib, uint32_t is `unsigned long` while
    # size_t is `unsigned int` — same width, distinct types — so template
    # argument deduction fails and every translation unit that instantiates
    # immer::set (i.e. everything touching state3/account_substate.hpp) fails
    # to compile. Upstream master still has this as of 2026-07-29, so bumping
    # the submodule does not help; the fix is to name the template argument.
    #
    # Rather than modify the pinned submodule — which would leave third_party/
    # dirty for everyone — generate a patched copy of the one header at
    # configure time and put it on the include path ahead of immer's own
    # directory. Same approach as build-support's patch_zkvm_ld, including the
    # anchor assertion: if a submodule bump moves this code, configuration
    # fails loudly here instead of silently compiling unpatched. Passed with
    # -isystem (via SYSTEM below) so immer keeps its system-header warning
    # suppression; a plain -I would win the search order but subject the copy
    # to -Werror.
    #
    # Remove this block once the fix is upstream and the submodule is bumped:
    #   https://github.com/arximboldi/immer — std::max<std::size_t> in
    #   immer/detail/hamts/node.hpp.
    set(_immer_node_rel "immer/detail/hamts/node.hpp")
    set(_immer_node_src "${THIRD_PARTY_DIR}/immer/${_immer_node_rel}")
    set(_immer_patch_dir "${CMAKE_CURRENT_BINARY_DIR}/immer-patched")
    set(_immer_node_dst "${_immer_patch_dir}/${_immer_node_rel}")

    file(READ "${_immer_node_src}" _immer_node_text)
    set(_immer_anchor "return std::max(sizeof(values_t),")
    string(FIND "${_immer_node_text}" "${_immer_anchor}" _immer_anchor_pos)
    if(_immer_anchor_pos EQUAL -1)
        message(FATAL_ERROR
            "immer layout changed (${_immer_node_src}): no `${_immer_anchor}` "
            "to patch. If upstream fixed sizeof_values_n, delete this block; "
            "otherwise update the anchor.")
    endif()
    string(REPLACE
        "${_immer_anchor}"
        "return std::max<std::size_t>(sizeof(values_t),"
        _immer_node_text "${_immer_node_text}")
    file(WRITE "${_immer_node_dst}" "${_immer_node_text}")

    # BUILD_INTERFACE because immer is an installable target: a build-directory
    # path may not appear in what it exports.
    target_include_directories(immer SYSTEM BEFORE
        INTERFACE "$<BUILD_INTERFACE:${_immer_patch_dir}>")

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
    # unconditionally `#include`s <blst.h> for the type aliases, but the
    # surviving zkVM TUs (precompiles.cpp, precompiles_gas_cost_impl.cpp)
    # don't call any blst_* function — precompiles_bls12.cpp is dropped.
    # So no link symbols are needed; just the header on the include path.
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

    set(ETHASH_BUILD_ETHASH OFF CACHE BOOL "" FORCE)
    set(ETHASH_TESTING OFF CACHE BOOL "" FORCE)
    set(ETHASH_INSTALL_CMAKE_CONFIG OFF CACHE BOOL "" FORCE)
    add_subdirectory("${THIRD_PARTY_DIR}/ethash" ethash)

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

    # The -print-file-name / -print-libgcc-file-name queries below resolve
    # per-multilib, so they must see the same -march/-mabi the guest is compiled
    # with. Without them a multilib toolchain answers for its *default* variant
    # and the extracted objects are silently the wrong ABI — an rv64 setjmp.o in
    # an rv32 archive, which only surfaces at link time.
    separate_arguments(_target_c_flags NATIVE_COMMAND "${CMAKE_C_FLAGS}")

    execute_process(
        COMMAND ${CMAKE_C_COMPILER} ${_target_c_flags} -print-file-name=libc.a
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

    # ---- Extract the needed compiler runtime routines from libgcc.a ----
    #
    # The guest links no libgcc, so any routine GCC lowers to a libcall has to
    # be carried in this archive. Members are located by the symbol they define
    # rather than by file name, because the file names are ABI-dependent:
    # __popcountdi2 lives in _popcountsi2.o for rv64 but _popcountdi2.o for
    # rv32, so a hardcoded name silently yields the wrong object (or, with a
    # multilib toolchain, the wrong ABI) and only fails at link time.
    #
    # This is the union over all guest ABIs, and is advisory: which routines GCC
    # actually emits libcalls for is ABI-dependent, and so is which ones libgcc
    # even contains. rv64 has no __popcountsi2 or __clzsi2 (it uses the DImode
    # routines), rv32 has no native 64-bit modulo and so needs __umoddi3. A
    # symbol absent from this target's libgcc is therefore normal and not an
    # error; the post-build check below is what enforces completeness, by
    # failing on anything the finished archive still needs and libgcc could have
    # supplied.
    set(_libgcc_syms
        __popcountsi2 __popcountdi2  # immer's HAMT bit math
        __clzsi2 __clzdi2            # std::countl_zero
        __bswapsi2 __bswapdi2        # std::byteswap
        __umoddi3                    # 64-bit modulo, a libcall on rv32
        __mulsf3 __fixunssfsi __floatunsisf  # soft float
    )

    execute_process(
        COMMAND ${CMAKE_C_COMPILER} ${_target_c_flags} -print-libgcc-file-name
        OUTPUT_VARIABLE _libgcc_a
        OUTPUT_STRIP_TRAILING_WHITESPACE
    )
    if(NOT EXISTS "${_libgcc_a}")
        message(FATAL_ERROR "libgcc.a not found via compiler query")
    endif()

    set(_libgcc_dir "${CMAKE_CURRENT_BINARY_DIR}/_libgcc_objs")
    file(REMOVE_RECURSE "${_libgcc_dir}")
    file(MAKE_DIRECTORY "${_libgcc_dir}")

    # `nm` on an archive prints a `member.o:` header before each member's
    # symbols. Two passes build the maps needed below: which member defines a
    # symbol, and which symbols a member leaves undefined.
    execute_process(
        COMMAND ${CMAKE_NM} --defined-only "${_libgcc_a}"
        OUTPUT_VARIABLE _nm_def OUTPUT_STRIP_TRAILING_WHITESPACE ERROR_QUIET)
    execute_process(
        COMMAND ${CMAKE_NM} --undefined-only "${_libgcc_a}"
        OUTPUT_VARIABLE _nm_undef OUTPUT_STRIP_TRAILING_WHITESPACE ERROR_QUIET)

    # _def_<sym> = defining member; _undef_<member> = symbols it needs.
    string(REPLACE "\n" ";" _lines "${_nm_def}")
    set(_member "")
    foreach(_line IN LISTS _lines)
        if(_line MATCHES "^(.+\\.o):$")
            set(_member "${CMAKE_MATCH_1}")
        elseif(_line MATCHES "[ \t]([A-Za-z_][A-Za-z0-9_]*)$")
            if(NOT DEFINED "_def_${CMAKE_MATCH_1}")
                set("_def_${CMAKE_MATCH_1}" "${_member}")
            endif()
        endif()
    endforeach()
    string(REPLACE "\n" ";" _lines "${_nm_undef}")
    set(_member "")
    foreach(_line IN LISTS _lines)
        if(_line MATCHES "^(.+\\.o):$")
            set(_member "${CMAKE_MATCH_1}")
        elseif(_line MATCHES "[ \t]([A-Za-z_][A-Za-z0-9_]*)$")
            list(APPEND "_undef_${_member}" "${CMAKE_MATCH_1}")
        endif()
    endforeach()

    # Transitive closure: an extracted member may itself need another libgcc
    # symbol (_popcountdi2.o calls __popcountsi2; the clz routines reference the
    # __clz_tab table), and the guest links no libgcc to satisfy them.
    set(_worklist "${_libgcc_syms}")
    set(_libgcc_members "")
    set(_seen_syms "")
    while(_worklist)
        list(POP_FRONT _worklist _sym)
        if("${_sym}" IN_LIST _seen_syms)
            continue()
        endif()
        list(APPEND _seen_syms "${_sym}")
        if(NOT DEFINED "_def_${_sym}")
            # Normal: this ABI's libgcc does not carry the routine, or it is
            # provided by a guest stub or the backend's Rust compiler_builtins.
            continue()
        endif()
        set(_m "${_def_${_sym}}")
        if(NOT "${_m}" IN_LIST _libgcc_members)
            list(APPEND _libgcc_members "${_m}")
            if(DEFINED "_undef_${_m}")
                list(APPEND _worklist ${_undef_${_m}})
            endif()
        endif()
    endwhile()
    foreach(_obj IN LISTS _libgcc_members)
        execute_process(
            COMMAND ${CMAKE_AR} x "${_libgcc_a}" "${_obj}"
            WORKING_DIRECTORY "${_libgcc_dir}"
        )
    endforeach()
    file(GLOB _libgcc_objs "${_libgcc_dir}/*.o")
    if(NOT _libgcc_objs)
        message(FATAL_ERROR "Failed to extract any objects from ${_libgcc_a}")
    endif()
    message(STATUS
        "zkvm: extracted libgcc members ${_libgcc_members} from ${_libgcc_a}")

    # ---- Verify the extracted objects match this target's ABI ----
    #
    # Completeness is not checkable here: the backends link Rust, whose
    # compiler_builtins supplies most of these routines, so the archive is
    # legitimately not self-contained (rv64 leaves __udivti3/__umodti3 to it).
    # What *is* checkable, and what silently broke before, is ABI: the
    # -print-*-file-name queries above resolve per-multilib, and if they answer
    # for the wrong variant the objects land in the archive with the wrong word
    # size and only fail at the backend's final link.
    #
    # Compare ELF class (byte 4 of e_ident: 1 = 32-bit, 2 = 64-bit) against a
    # freshly compiled probe, which is by definition this target's ABI.
    set(_probe_c "${CMAKE_CURRENT_BINARY_DIR}/_abi_probe.c")
    set(_probe_o "${CMAKE_CURRENT_BINARY_DIR}/_abi_probe.o")
    file(WRITE "${_probe_c}" "int _monad_abi_probe;\n")
    execute_process(
        COMMAND ${CMAKE_C_COMPILER} ${_target_c_flags} -c "${_probe_c}"
                -o "${_probe_o}"
        RESULT_VARIABLE _probe_rc)
    if(NOT _probe_rc EQUAL 0)
        message(FATAL_ERROR "failed to compile the ABI probe object")
    endif()
    file(READ "${_probe_o}" _probe_ident HEX LIMIT 5)
    string(SUBSTRING "${_probe_ident}" 8 2 _want_elf_class)

    foreach(_obj IN LISTS _libc_objs _libgcc_objs)
        file(READ "${_obj}" _obj_ident HEX LIMIT 5)
        string(SUBSTRING "${_obj_ident}" 8 2 _obj_elf_class)
        if(NOT _obj_elf_class STREQUAL _want_elf_class)
            message(FATAL_ERROR
                "${_obj} is ELF class 0x${_obj_elf_class} but this target "
                "compiles to ELF class 0x${_want_elf_class} (01 = 32-bit, "
                "02 = 64-bit). The toolchain answered -print-file-name for the "
                "wrong multilib: check that it has a variant matching "
                "'${CMAKE_C_FLAGS}' (riscv64-unknown-elf-gcc -print-multi-lib).")
        endif()
    endforeach()

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
    )
    monad_compile_options(monad-core)
    monad_riscv_compile_options(monad-core)
    target_link_libraries(monad-core PUBLIC evmc)
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
        ethash::keccak
        intx::intx
        quill::quill
        silkpre
        TBB::tbb)

    # zkVM replacement for ecrecover.cpp — routes through zkvm_secp256k1_ecrecover.
    target_sources(monad_execution_ethereum PRIVATE
        "${MONAD_ROOT}/zkvm/category/execution/ethereum/core/ecrecover.cpp"
    )

    # db/util.cpp is dropped (pulls in category/mpt + nlohmann/json); provide
    # just the two RLP encoders commit_builder.cpp needs from it.
    target_sources(monad_execution_ethereum PRIVATE
        "${MONAD_ROOT}/zkvm/category/execution/ethereum/db/util.cpp"
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
        PUBLIC keccak
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
    # ...but keep the MSM gas-cost tables from it: precompiles_gas_cost_impl.cpp
    # (retained) calls bls12::msm_discount<G1/G2> for Prague+, and those are
    # pure lookups with no blst dependency. The shadow provides just them; the
    # blst-backed execute paths stay dropped.
    target_sources(monad_precompiles PRIVATE
        "${MONAD_ROOT}/zkvm/category/execution/ethereum/precompiles_bls12.cpp")
    monad_zkvm_drop_libraries(monad_precompiles
        monad-vm
        monad_core
        monad_crypto
        c-kzg-4844
        PkgConfig::crypto++
        ethash::keccak
        intx::intx
        silkpre)
    target_link_libraries(monad_precompiles
        PUBLIC komihash
        PUBLIC cthash
        PUBLIC keccak
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
    # libsecp256k1, fiber dispatch, event-ring recorder, disk-page storage.
    monad_zkvm_drop_sources(monad_execution_native
        "db/storage_page.cpp"
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
