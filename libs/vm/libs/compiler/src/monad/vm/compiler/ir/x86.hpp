#pragma once

#include <monad/vm/compiler/ir/basic_blocks.hpp>
#include <monad/vm/compiler/ir/x86/types.hpp>

#include <asmjit/x86.h>

#include <evmc/evmc.h>

#include <memory>
#include <span>

namespace monad::vm::compiler::native
{
    /**
     * Compile the given contract and add it to JitRuntime.
     */
    std::shared_ptr<Nativecode> compile(
        asmjit::JitRuntime &rt, std::span<uint8_t const> contract,
        evmc_revision rev, CompilerConfig const & = {});

    /**
     * Compile given IR and add it to the JitRuntime.
     */
    std::shared_ptr<Nativecode> compile_basic_blocks(
        evmc_revision rev, asmjit::JitRuntime &rt,
        basic_blocks::BasicBlocksIR const &ir, CompilerConfig const & = {});

    /**
     * Upper bound on (estimated) native contract size in bytes.
     */
    constexpr uint64_t
    max_code_size(uint32_t offset, size_t bytecode_size) noexcept
    {
        // A contract will be compiled asynchronously after the accumulated
        // execution gas cost of interpretation reaches this threshold. If
        // byte code size is 128kB, then the interpreter will need to use
        // more than 4 million gas on this contract before it will be
        // compiled, when `offset` is zero. There is a theoretical hard
        // upper bound on native code size to ensure that the emitter
        // will not overflow relative x86 memory addressing offsets.
        return std::min(
            offset + 32 * uint64_t{bytecode_size}, code_size_hard_upper_bound);
    }
}
