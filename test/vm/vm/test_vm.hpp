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

#include "state.hpp"
#include "test_state.hpp"

#include <category/vm/compiler/ir/x86.hpp>
#include <category/vm/core/assert.h>
#include <category/vm/runtime/types.hpp>
#include <category/vm/utils/debug.hpp>
#include <category/vm/vm.hpp>

#include <evmc/evmc.hpp>

#include <evmone/baseline.hpp>
#include <evmone/constants.hpp>
#include <evmone/vm.hpp>

#include <unordered_map>

#ifdef MONAD_COMPILER_LLVM
    #include <category/vm/llvm/llvm.hpp>
#endif

class BlockchainTestVM : public evmc_vm
{
public:
    enum class Implementation
    {
        Compiler,
        Interpreter,
        Evmone,
#ifdef MONAD_COMPILER_LLVM
        LLVM,
#endif
    };

    template <typename V>
    using CodeMap = std::unordered_map<
        evmc::bytes32, V, monad::vm::utils::Hash32Hash,
        monad::vm::utils::Bytes32Equal>;

    BlockchainTestVM(
        Implementation impl,
        monad::vm::compiler::native::PreEmitterHook pre_instruction_emit_hook =
            nullptr,
        monad::vm::compiler::native::PostEmitterHook
            post_instruction_emit_hook = nullptr);

    evmc::Result execute(
        evmc_host_interface const *host, evmc_host_context *context,
        evmc_revision rev, evmc_message const *msg, uint8_t const *code,
        size_t code_size);

    static constexpr std::string_view
    impl_name(BlockchainTestVM::Implementation const impl) noexcept
    {
        switch (impl) {
        case Implementation::Interpreter:
            return "interpreter";
        case Implementation::Compiler:
            return "compiler";
        case Implementation::Evmone:
            return "evmone";
#ifdef MONAD_COMPILER_LLVM
        case Implementation::LLVM:
            return "llvm";
#endif
        }

        std::unreachable();
    };

    void precompile_contract(
        evmc_revision rev, evmc::bytes32 const &code_hash, uint8_t const *code,
        size_t const code_size,
        [[maybe_unused]] BlockchainTestVM::Implementation const impl);

    void precompile_contracts(
        evmc_revision rev, evmone::test::TestState const &state,
        BlockchainTestVM::Implementation const impl);

    Implementation implementation() const
    {
        return impl_;
    }

private:
    Implementation impl_;
    evmone::VM evmone_vm_;
    monad::vm::VM monad_vm_;
    char const *debug_dir_;
    monad::vm::CompilerConfig base_config;
    CodeMap<evmone::baseline::CodeAnalysis> code_analyses_;
    CodeMap<monad::vm::SharedIntercode> intercodes_;
#ifdef MONAD_COMPILER_LLVM
    monad::vm::llvm::VM llvm_vm_;
#endif

    evmone::baseline::CodeAnalysis const &get_code_analysis(
        evmc::bytes32 const &code_hash, uint8_t const *code, size_t code_size);

    monad::vm::SharedIntercode const &get_intercode(
        evmc::bytes32 const &code_hash, uint8_t const *code, size_t code_size);

    std::pair<
        monad::vm::SharedIntercode const &,
        monad::vm::SharedNativecode const> const
    get_intercode_nativecode(
        evmc_revision const rev, evmc::bytes32 const &code_hash,
        uint8_t const *code, size_t code_size);

    evmc::Result execute_evmone(
        evmc_host_interface const *host, evmc_host_context *context,
        evmc_revision rev, evmc_message const *msg, uint8_t const *code,
        size_t code_size);

    evmc::Result execute_compiler(
        evmc_host_interface const *host, evmc_host_context *context,
        evmc_revision rev, evmc_message const *msg, uint8_t const *code,
        size_t code_size);

    evmc::Result execute_interpreter(
        evmc_host_interface const *host, evmc_host_context *context,
        evmc_revision rev, evmc_message const *msg, uint8_t const *code,
        size_t code_size);

#ifdef MONAD_COMPILER_LLVM
    void cache_llvm(
        evmc_revision const rev, evmc::bytes32 const &code_hash,
        uint8_t const *code, size_t code_size);

    evmc::Result execute_llvm(
        evmc_host_interface const *host, evmc_host_context *context,
        evmc_revision rev, evmc_message const *msg, uint8_t const *code,
        size_t code_size);
#endif
};
