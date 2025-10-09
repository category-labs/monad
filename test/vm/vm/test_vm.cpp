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

#include "test_vm.hpp"
#include "hash_utils.hpp"
#include "test_state.hpp"

#include <category/vm/code.hpp>
#include <category/vm/compiler/ir/x86/types.hpp>
#include <category/vm/core/assert.h>
#include <category/vm/evm/switch_traits.hpp>

#include <category/vm/utils/evmc_utils.hpp>
#include <category/vm/vm.hpp>

#ifdef MONAD_COMPILER_LLVM
    #include <category/vm/llvm/llvm.hpp>
    #include <llvm-c/Target.h>
#endif

#include <evmc/evmc.h>
#include <evmc/evmc.hpp>

#include <evmone/baseline.hpp>

#include <cstddef>
#include <cstdint>
#include <cstdlib>
#include <cstring>
#include <filesystem>
#include <iostream>
#include <limits>
#include <sstream>
#include <utility>

using namespace monad;
using namespace monad::vm::compiler;
using namespace monad::vm::interpreter;

using namespace evmc::literals;

namespace fs = std::filesystem;

#ifdef MONAD_COMPILER_LLVM
void init_llvm()
{
    LLVMInitializeNativeTarget();
    LLVMInitializeNativeAsmPrinter();
}
#endif

namespace
{

#ifdef MONAD_COMPILER_LLVM
    using namespace monad::vm::llvm;
#endif

    constexpr auto SYSTEM_ADDRESS =
        0xfffffffffffffffffffffffffffffffffffffffe_address;

    void destroy(evmc_vm *vm)
    {
        delete reinterpret_cast<BlockchainTestVM *>(vm);
    }

    evmc_result execute(
        evmc_vm *vm, evmc_host_interface const *host,
        evmc_host_context *context, evmc_revision rev, evmc_message const *msg,
        uint8_t const *code, size_t code_size)
    {
        return reinterpret_cast<BlockchainTestVM *>(vm)
            ->execute(host, context, rev, msg, code, code_size)
            .release_raw();
    }

    evmc_capabilities_flagset get_capabilities(evmc_vm *)
    {
        return EVMC_CAPABILITY_EVM1;
    }

    BlockchainTestVM::Implementation
    impl_from_env(BlockchainTestVM::Implementation const impl) noexcept
    {
        static auto *const evmone_vm_only_env =
            std::getenv("MONAD_COMPILER_EVMONE_ONLY");
        static bool const evmone_vm_only =
            evmone_vm_only_env && std::strcmp(evmone_vm_only_env, "1") == 0;
        if (evmone_vm_only) {
            return BlockchainTestVM::Implementation::Evmone;
        }

        return impl;
    }

    bool is_compiler_runtime_debug_trace_enabled()
    {
        static auto *const debug_trace_env =
            std::getenv("MONAD_COMPILER_DEBUG_TRACE");
        static bool const debug_trace =
            debug_trace_env && std::strcmp(debug_trace_env, "1") == 0;
        return debug_trace;
    }
}

BlockchainTestVM::BlockchainTestVM(
    Implementation impl, native::EmitterHook post_hook, std::function<void(evmc_message const *msg)> execute_hook)
    : evmc_vm{EVMC_ABI_VERSION, "monad-compiler-blockchain-test-vm", "0.0.0", ::destroy, ::execute, ::get_capabilities, nullptr}
    , impl_{impl_from_env(impl)}
    , debug_dir_{std::getenv("MONAD_COMPILER_ASM_DIR")}
    , execute_hook_{execute_hook}
    , base_config{
          .runtime_debug_trace = is_compiler_runtime_debug_trace_enabled(),
          .max_code_size_offset = code_size_t::max(),
          .post_instruction_emit_hook = post_hook}
{
    MONAD_VM_ASSERT(!debug_dir_ || fs::is_directory(debug_dir_));
}

evmc::Result BlockchainTestVM::execute(
    evmc_host_interface const *host, evmc_host_context *context,
    evmc_revision rev, evmc_message const *msg, uint8_t const *code,
    size_t code_size)
{
    if (execute_hook_) {
        execute_hook_(msg);
    }
    if (msg->kind == EVMC_CREATE || msg->kind == EVMC_CREATE2 ||
        msg->sender == SYSTEM_ADDRESS) {
        return evmc::Result{evmone_vm_.execute(
            &evmone_vm_, host, context, rev, msg, code, code_size)};
    }
    else if (impl_ == Implementation::Evmone) {
        return execute_evmone(host, context, rev, msg, code, code_size);
    }
    else if (impl_ == Implementation::Compiler) {
        return execute_compiler(host, context, rev, msg, code, code_size);
    }
#ifdef MONAD_COMPILER_LLVM
    else if (impl_ == Implementation::LLVM) {
        return execute_llvm(host, context, rev, msg, code, code_size);
    }
#endif
    else {
        MONAD_VM_ASSERT(impl_ == Implementation::Interpreter);
        return execute_interpreter(host, context, rev, msg, code, code_size);
    }
}

evmone::baseline::CodeAnalysis const &BlockchainTestVM::get_code_analysis(
    evmc::bytes32 const &code_hash, uint8_t const *code, size_t code_size)
{
    auto it1 = code_analyses_.find(code_hash);
    if (it1 != code_analyses_.end()) {
        return it1->second;
    }
    auto [it2, b] = code_analyses_.insert(
        {code_hash, evmone::baseline::analyze({code, code_size}, false)});
    MONAD_VM_ASSERT(b);
    return it2->second;
}

monad::vm::SharedIntercode const &BlockchainTestVM::get_intercode(
    evmc::bytes32 const &code_hash, uint8_t const *code, size_t code_size)
{
    auto it1 = intercodes_.find(code_hash);
    if (it1 != intercodes_.end()) {
        return it1->second;
    }
    auto [it2, b] = intercodes_.insert(
        {code_hash, monad::vm::make_shared_intercode(code, code_size)});
    MONAD_VM_ASSERT(b);
    return it2->second;
}

std::pair<
    monad::vm::SharedIntercode const &, monad::vm::SharedNativecode const> const
BlockchainTestVM::get_intercode_nativecode(
    evmc_revision const rev, evmc::bytes32 const &code_hash,
    uint8_t const *code, size_t code_size)
{
    auto const &icode = get_intercode(code_hash, code, code_size);

    monad::vm::SharedNativecode ncode;
    if (debug_dir_) {
        std::ostringstream file(std::ostringstream::ate);
        file.str(debug_dir_);
        file << '/';
        file << monad::vm::utils::hex_string(code_hash);
        native::CompilerConfig config{base_config};
        auto asm_log_path = file.str();
        config.asm_log_path = asm_log_path.c_str();
        ncode = [&] {
            SWITCH_EVM_TRAITS(
                monad_vm_.compiler().cached_compile, code_hash, icode, config);
            MONAD_VM_ASSERT(false);
        }();
    }
    else {
        ncode = [&] {
            SWITCH_EVM_TRAITS(
                monad_vm_.compiler().cached_compile,
                code_hash,
                icode,
                base_config);
            MONAD_VM_ASSERT(false);
        }();
    }

    return {icode, ncode};
}

void BlockchainTestVM::precompile_contract(
    evmc_revision rev, evmc::bytes32 const &code_hash, uint8_t const *code,
    size_t const code_size,
    [[maybe_unused]] BlockchainTestVM::Implementation const impl)
{
    (void)get_code_analysis(code_hash, code, code_size);
    (void)get_intercode_nativecode(rev, code_hash, code, code_size);
#ifdef MONAD_COMPILER_LLVM
    if (impl == Implementation::LLVM) {
        cache_llvm(rev, code_hash, code, code_size);
    }
#endif
}

void BlockchainTestVM::precompile_contracts(
    evmc_revision rev, evmone::test::TestState const &state,
    BlockchainTestVM::Implementation const impl)
{
    for (auto const &[_, account] : state) {
        auto const &code = account.code.data();
        auto const &code_size = account.code.size();
        auto const &code_hash = evmone::keccak256({code, code_size});
        precompile_contract(rev, code_hash, code, code_size, impl);
    }
}

evmc::Result BlockchainTestVM::execute_evmone(
    evmc_host_interface const *host, evmc_host_context *context,
    evmc_revision rev, evmc_message const *msg, uint8_t const *code,
    size_t code_size)
{
    auto code_hash = host->get_code_hash(context, &msg->code_address);
    auto const &a = get_code_analysis(code_hash, code, code_size);
    return evmc::Result{
        evmone::baseline::execute(evmone_vm_, *host, context, rev, *msg, a)};
}

evmc::Result BlockchainTestVM::execute_compiler(
    evmc_host_interface const *host, evmc_host_context *context,
    evmc_revision rev, evmc_message const *msg, uint8_t const *code,
    size_t code_size)
{
    auto code_hash = host->get_code_hash(context, &msg->code_address);
    auto const &[icode, ncode] =
        get_intercode_nativecode(rev, code_hash, code, code_size);

    if (base_config.runtime_debug_trace) {
        std::cout << "Address " << vm::utils::hex_string(msg->code_address)
                  << " => Hash " << vm::utils::hex_string(code_hash)
                  << std::endl;
    }

    MONAD_VM_ASSERT(ncode->entrypoint() != nullptr)
    return monad_vm_.execute_native_entrypoint_raw(
        host, context, msg, icode, ncode->entrypoint());
}

#ifdef MONAD_COMPILER_LLVM
void BlockchainTestVM::cache_llvm(
    evmc_revision const rev, evmc::bytes32 const &code_hash,
    uint8_t const *code, size_t code_size)
{
    llvm_vm_.cache_llvm(rev, code_hash, code, code_size);
}

evmc::Result BlockchainTestVM::execute_llvm(
    evmc_host_interface const *host, evmc_host_context *context,
    evmc_revision rev, evmc_message const *msg, uint8_t const *code,
    size_t code_size)
{
    auto code_hash = host->get_code_hash(context, &msg->code_address);

    return llvm_vm_.execute_llvm(
        rev, code_hash, host, context, msg, code, code_size);
}
#endif

evmc::Result BlockchainTestVM::execute_interpreter(
    evmc_host_interface const *host, evmc_host_context *context,
    evmc_revision rev, evmc_message const *msg, uint8_t const *code,
    size_t code_size)
{
    auto code_hash = host->get_code_hash(context, &msg->code_address);
    auto const &icode = get_intercode(code_hash, code, code_size);
    SWITCH_EVM_TRAITS(
        monad_vm_.execute_intercode_raw, host, context, msg, icode);
    MONAD_VM_ASSERT(false);
}
