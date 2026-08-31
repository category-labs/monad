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

    # Fail-closed profile for a report/release ZisK artifact. Diagnostic A/B
    # builds keep using the individual switches below; an official artifact
    # enables this one switch and cannot silently omit a measured lever.
    option(MONAD_ZKVM_OFFICIAL_PROFILE
           "build the audited, fail-closed official ZisK guest profile" OFF)
    if(MONAD_ZKVM_OFFICIAL_PROFILE)
        if(NOT MONAD_ZKVM_GUEST_TARGET STREQUAL "zisk")
            message(FATAL_ERROR
                "MONAD_ZKVM_OFFICIAL_PROFILE is a ZisK-only build profile")
        endif()
        # NO_DIRTY_ACCOUNTS and NO_MERGE_CONSTRAINTS are here rather than left to the caller for
        # the same reason as the rest: an official artifact must not be able to silently omit a
        # measured lever. Both remove work whose only readers are outside the guest -- the state
        # tracer this file excludes, and the can_merge the sequential path does not call.
        foreach(_required MONAD_ZKVM_ZISK_DMA MONAD_ZKVM_TABLE_ARG MONAD_ZKVM_FUSE
                          MONAD_ZKVM_NO_DIRTY_ACCOUNTS MONAD_ZKVM_NO_MERGE_CONSTRAINTS
                          MONAD_ZKVM_VARCODE_CACHE MONAD_ZKVM_WIDE_MEMORY_SIZE)
            if(DEFINED ${_required} AND NOT ${_required})
                message(FATAL_ERROR
                    "${_required}=OFF contradicts MONAD_ZKVM_OFFICIAL_PROFILE=ON")
            endif()
            set(${_required} ON CACHE BOOL "required by the official ZisK profile" FORCE)
        endforeach()
        if(DEFINED MONAD_ZKVM_KECCAKF_MEMO AND NOT MONAD_ZKVM_KECCAKF_MEMO)
            message(FATAL_ERROR
                "MONAD_ZKVM_KECCAKF_MEMO=OFF contradicts MONAD_ZKVM_OFFICIAL_PROFILE=ON")
        endif()
        set(MONAD_ZKVM_KECCAKF_MEMO ON CACHE BOOL
            "required by the official ZisK profile" FORCE)
        # CHECK_SEQUENTIAL_MERGE is already forbidden here, which is also what keeps it from
        # colliding with the NO_MERGE_CONSTRAINTS forced on just above.
        if(MONAD_ZKVM_KECCAK_SITES OR MONAD_ZKVM_SELFTEST
           OR MONAD_ZKVM_CHECK_SEQUENTIAL_MERGE)
            message(FATAL_ERROR
                "diagnostic counters/self-test are forbidden in the official ZisK profile")
        endif()
        add_compile_definitions(MONAD_ZKVM_OFFICIAL_PROFILE=1)
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
        " -finline-functions")

    set(_guest_target "monad-zkvm-guest-${MONAD_ZKVM_GUEST_TARGET}")

    # The SP1 and ZisK ripemd160 accelerators place the digest at opposite
    # ends of their 32-byte output word, so the precompile shim normalises
    # them differently (zkvm/category/execution/ethereum/precompiles_impl.hpp).
    # Expose the backend as a compile definition for that per-backend branch.
    # Diagnostic: per-site keccak counters appended to the public values. Off by default, so the
    # shipped guest carries neither the counter array nor the increments. Enable with
    #   -DMONAD_ZKVM_KECCAK_SITES=ON
    # then read the tail after the three 32-byte roots: N_SITES little-endian u32 call counts
    # followed by as many permutation counts, in the order given by
    # zkvm/category/core/keccak_sites.hpp. The roots stay at offsets 0/32/64, so ev.sh is unaffected and a
    # reporting run is still a verified run. Exists because ziskemu's call-path grouping misplaces
    # 96 % of the block's duplicate hashes; a counter on the hashing line cannot.
    # Lever: the per-frame dirty-account list is write-only in the guest, so compile it away.
    # pop_reject moves it out and never reads it; pop_accept reads it only to fill the parent's copy
    # of the same list; and its one external reader, trace/state_tracer.cpp, is in this file's own
    # exclusion list, with no symbol for it or for StateTracer in the shipped ELF. Declared only
    # here, so the host build keeps both the list and the tracer that uses it.
    option(MONAD_ZKVM_NO_DIRTY_ACCOUNTS
           "compile away the per-frame dirty-account list, which the guest never reads" OFF)
    if(MONAD_ZKVM_NO_DIRTY_ACCOUNTS)
        add_compile_definitions(MONAD_ZKVM_NO_DIRTY_ACCOUNTS)
    endif()

    option(MONAD_ZKVM_KECCAK_SITES "count keccak calls per call site" OFF)
    if(MONAD_ZKVM_KECCAK_SITES)
        add_compile_definitions(MONAD_ZKVM_KECCAK_SITES)
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

    # Lever: stop writing the merge constraints, whose only reader is can_merge.
    # State::get_balance resolved the ORIGINAL row purely to stamp one, where get_nonce reads through
    # the cheap accessor; record_balance_constraint_for_debit does the same plus a uint256 subtraction,
    # and its caller uses only the return value -- the sender-has-balance predicate, which is semantic
    # and stays. Declared only here, so the host keeps the constraints its scheduler needs.
    #
    # Mutually exclusive with CHECK_SEQUENTIAL_MERGE by construction: that flag restores can_merge as
    # an assertion, and an assertion reading constraints nobody wrote would fail for the wrong reason.
    # Lever: give the guest's VM shadow the varcode cache the host has. The shadow's find_varcode
    # returns nullopt unconditionally, so every read of an existing contract rebuilds a Varcode and
    # its control block out of an intercode BlockState::code_ already holds. The bytecode itself is
    # not re-decoded: what repeats is the wrapper, not the analysis.
    option(MONAD_ZKVM_VARCODE_CACHE
           "cache varcodes by code hash in the guest's VM shadow" OFF)
    if(MONAD_ZKVM_VARCODE_CACHE)
        add_compile_definitions(MONAD_ZKVM_VARCODE_CACHE)
    endif()

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

    if(MONAD_ZKVM_GUEST_TARGET STREQUAL "sp1")
        add_compile_definitions(MONAD_ZKVM_SP1)
    endif()
    if(MONAD_ZKVM_GUEST_TARGET STREQUAL "zisk")
        add_compile_definitions(MONAD_ZKVM_ZISK)

        # Memoise Keccak-f through ZisK's executor-side index (fcall 24/25),
        # zkvm/guest/keccak_accel.cpp. ~14 % of a block's permutations repeat
        # a state, and the lookup costs the guest nothing the cost model
        # charges for. OFF compiles the mechanism out — table, fcalls and
        # branch — so it is a control arm and not a disabled predicate:
        #   -DMONAD_ZKVM_KECCAKF_MEMO=OFF
        # It costs 100 MiB of .bss, which is why it is a switch at all.
        option(MONAD_ZKVM_KECCAKF_MEMO "memoise Keccak-f via the ZisK executor index" ON)
        if(MONAD_ZKVM_KECCAKF_MEMO)
            add_compile_definitions(MONAD_ZKVM_KECCAKF_MEMO=1)
        else()
            add_compile_definitions(MONAD_ZKVM_KECCAKF_MEMO=0)
        endif()
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
        string(APPEND CMAKE_C_FLAGS " -mtune=generic-ooo")
        string(APPEND CMAKE_CXX_FLAGS " -mtune=generic-ooo")

        # ZisK 1.1 transpiles the RISC-V B extension; 1.0 did not. Zbb and Zbs
        # are wired unconditionally, so widening -march lets gcc emit rev8,
        # cpop, clz, andn and the single-bit ops instead of open-coding them --
        # 2454 rev8 and 1047 bseti sites in the linked guest. Zba, Zbc, Zbkc
        # and Zbkx sit behind cargo features the published emulator is built
        # without: a guest carrying sh2add aborts the transpiler, so they stay
        # out until the shipped binary enables them.
        #
        # -march here rather than in the shared riscv64-elf toolchain: the
        # widening is only sound for a runtime known to implement these, and
        # ZisK is the only backend established to. 504 of 504 corpus blocks
        # give the recorded post-state root with this on.
        # Zbkb rides along with Zbb and Zbs. The shipped emulator transpiles it — the reference
        # C++ guest (0xPolygonHermez/ziskethone) enables it and reproduces its block hashes under
        # ziskemu 1.1.0-alpha — so the reason Zba, Zbc, Zbkc and Zbkx stay out does not apply to
        # it. Measured over 200 mainnet blocks it is worth 0.1% (-0.08% steps, -0.06% COST). Kept
        # because the guest should carry every extension the runtime is known to implement, not
        # because it pays.
        # Zicsr carries no codegen of its own -- gcc never reaches for a CSR on
        # its own account -- but the DMA lowering below emits `csrs 0x813,src`
        # and the assembler rejects it without the extension named. Verified
        # inert: with Zicsr and without the lowering the guest is identical to
        # the build before it, step for step and cost for cost.
        string(APPEND CMAKE_C_FLAGS " -march=rv64ima_zbb_zbs_zbkb_zicsr")
        string(APPEND CMAKE_CXX_FLAGS " -march=rv64ima_zbb_zbs_zbkb_zicsr")

        # Block memory operations through ZisK's DMA precompile, rather than a
        # call into the ziskos mem* thunk or an inline load/store run.
        #
        # OFF because it needs a patched compiler: the backend lowering is not
        # upstream gcc. Build one with
        # profiling/experiments/zisk-dma-gcc15/build-gcc15.sh in zkvm-bench,
        # point RISCV_TOOLCHAIN_DIR at it, and turn this on. A stock compiler
        # rejects the flag outright rather than silently ignoring it, so a build
        # that forgets the toolchain fails loudly.
        #
        # It reaches copies no source change can: evmc_bytes32 is uint8_t[32]
        # with alignment 1, so a plain struct assignment cannot use word moves
        # and gcc emits a libcall -- with a frame, and the arguments marshalled
        # into a0/a1/a2. The marker takes the same copy in one instruction.
        option(MONAD_ZKVM_ZISK_DMA "lower block mem* to the ZisK DMA precompile" OFF)
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

        # Thread the interpreter's dispatch table base through the tail-call chain as a seventh
        # argument, instead of re-materialising it at every opcode (GCC emits `auipc` plus an `ld`
        # from a constant pool, 3,129,627 steps a block on r10-dma over the canonical 200, 3.21 % of
        # the guest, doing no EVM work). Measured: steps -2.771 % median, 200 of 200 blocks
        # improving, 200 of 200 post-state roots.
        #
        # An earlier variant pinned the base in s11 instead. It is 0.16 points faster and was
        # dropped anyway: a nested interpreter entry overwrites the register, sound only because one
        # block cannot nest an execution with different `traits`, and that invariant could not be
        # validated with the corpora on hand. Threading the base as an argument has no invariant to
        # validate. The s11 path survives in types.hpp behind the raw -DMONAD_VM_PINNED_TABLE so the
        # published comparison can be re-run; it is deliberately NOT a build option, and landing
        # should delete it.
        #
        # Guarded rather than global: under Clang the right answer is preserve_none, which the
        # interpreter already asks for through MONAD_VM_INSTRUCTION_CALL and which removes the
        # reload this option targets, so a Clang build must not silently take a second, weaker path.
        option(MONAD_ZKVM_TABLE_ARG
               "thread the interpreter dispatch table base as a seventh argument" OFF)
        if(MONAD_ZKVM_TABLE_ARG)
            if(NOT CMAKE_SYSTEM_PROCESSOR MATCHES "riscv")
                message(FATAL_ERROR
                    "MONAD_ZKVM_TABLE_ARG is measured on the RISC-V guest, where the seventh "
                    "argument is passed in a register (a0-a7). On a target with fewer argument "
                    "registers it can cost a stack slot per dispatch. Got "
                    "CMAKE_SYSTEM_PROCESSOR='${CMAKE_SYSTEM_PROCESSOR}'.")
            endif()
            if(NOT CMAKE_CXX_COMPILER_ID STREQUAL "GNU")
                message(FATAL_ERROR
                    "MONAD_ZKVM_TABLE_ARG is for the GCC guest only. Clang supports preserve_none, "
                    "which the interpreter uses through MONAD_VM_INSTRUCTION_CALL and which removes "
                    "the reload this option targets. Got "
                    "CMAKE_CXX_COMPILER_ID='${CMAKE_CXX_COMPILER_ID}'.")
            endif()
            add_compile_definitions(MONAD_VM_TABLE_ARG)
        endif()

        # Fused superinstructions: sequences that always run back to back pay two
        # dispatches, two gas checks and a 256-bit stack round trip, and run here as
        # one step. Measured on the canonical 200 on top of MONAD_ZKVM_TABLE_ARG:
        # steps -4.498 % median, COST -2.131 %, every block improving, 200 of 200
        # post-state roots.
        #
        # Enables the four fusions that measured positive. The per-fusion macros
        # stay available as raw -D so one can be dropped to re-measure it:
        # MONAD_VM_FUSE_JUMPDEST, _PUSH1OP, _PUSH2JUMP, _TESTJUMPI. POP+POP was
        # measured and is deliberately absent -- its gate costs more than the one
        # dispatch it saves.
        option(MONAD_ZKVM_FUSE
               "fuse hot opcode sequences into single interpreter steps" OFF)
        if(MONAD_ZKVM_FUSE)
            if(NOT CMAKE_CXX_COMPILER_ID STREQUAL "GNU")
                message(FATAL_ERROR
                    "MONAD_ZKVM_FUSE is measured on the GCC guest only. Got "
                    "CMAKE_CXX_COMPILER_ID='${CMAKE_CXX_COMPILER_ID}'.")
            endif()
            add_compile_definitions(
                MONAD_VM_FUSE_JUMPDEST
                MONAD_VM_FUSE_PUSH1OP
                MONAD_VM_FUSE_PUSH2JUMP
                MONAD_VM_FUSE_TESTJUMPI)
        endif()

        if(MONAD_ZKVM_OFFICIAL_PROFILE)
            if(NOT CMAKE_CXX_COMPILER_ID STREQUAL "GNU" OR
               NOT CMAKE_CXX_COMPILER_VERSION VERSION_EQUAL "15.2.0")
                message(FATAL_ERROR
                    "official ZisK profile requires GCC 15.2.0; got "
                    "${CMAKE_CXX_COMPILER_ID} ${CMAKE_CXX_COMPILER_VERSION}")
            endif()
            file(SHA256 "${CMAKE_CXX_COMPILER}" _official_cxx_sha256)
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
            set(_official_git_commit "${MONAD_ZKVM_GIT_COMMIT}")
            string(SHA256 _official_build_signature
                "${_official_cxx_sha256}\n${CMAKE_C_FLAGS}\n${CMAKE_C_FLAGS_RELEASE}\n${CMAKE_CXX_FLAGS}\n${CMAKE_CXX_FLAGS_RELEASE}")
            add_compile_definitions(
                MONAD_ZKVM_BUILD_COMMIT="${_official_git_commit}"
                MONAD_ZKVM_BUILD_SIGNATURE="${_official_build_signature}")
            file(WRITE "${CMAKE_BINARY_DIR}/monad-zkvm-official-profile.json"
                "{\n"
                "  \"schema\": 1,\n"
                "  \"compiler\": \"${CMAKE_CXX_COMPILER}\",\n"
                "  \"compiler_id\": \"${CMAKE_CXX_COMPILER_ID}\",\n"
                "  \"compiler_version\": \"${CMAKE_CXX_COMPILER_VERSION}\",\n"
                "  \"compiler_sha256\": \"${_official_cxx_sha256}\",\n"
                "  \"commit\": \"${_official_git_commit}\",\n"
                "  \"build_signature\": \"${_official_build_signature}\",\n"
                "  \"c_flags\": \"${CMAKE_C_FLAGS}\",\n"
                "  \"c_flags_release\": \"${CMAKE_C_FLAGS_RELEASE}\",\n"
                "  \"cxx_flags\": \"${CMAKE_CXX_FLAGS}\",\n"
                "  \"cxx_flags_release\": \"${CMAKE_CXX_FLAGS_RELEASE}\",\n"
                "  \"dma\": true,\n"
                "  \"table_arg\": true,\n"
                "  \"keccakf_memo\": true,\n"
                "  \"fuse\": true\n"
                "}\n")
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

    # The map's load-factor arithmetic is float, and the guest has no FPU.
    # Rewrite it to integer in a derived copy of the header, and shadow the
    # submodule's on the include path -- 0.236 % of the block, submodule left
    # pristine. See the module for why this is not a submodule patch.
    include("${CMAKE_CURRENT_SOURCE_DIR}/unordered_dense_no_float.cmake")
    monad_zkvm_unordered_dense_no_float(unordered_dense "${THIRD_PARTY_DIR}"
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
        ethash::keccak
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

    add_library(${_guest_target} STATIC
        ${_selftest_sources}
        "${CMAKE_CURRENT_SOURCE_DIR}/ffi.cpp"
        "${CMAKE_CURRENT_SOURCE_DIR}/execute_block_zkvm.cpp"
        "${CMAKE_CURRENT_SOURCE_DIR}/body_roots.cpp"
        "${CMAKE_CURRENT_SOURCE_DIR}/keccak_accel.cpp"
        "${CMAKE_CURRENT_SOURCE_DIR}/mem_sp1.cpp"
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
        "${CMAKE_CURRENT_SOURCE_DIR}/keccak_accel.cpp"
        "${CMAKE_CURRENT_SOURCE_DIR}/mem_sp1.cpp"
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
