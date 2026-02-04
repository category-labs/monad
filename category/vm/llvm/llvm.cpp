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

#include <category/core/runtime/uint256.hpp>
#include <category/vm/compiler/ir/basic_blocks.hpp>
#include <category/vm/evm/explicit_traits.hpp>
#include <category/vm/evm/switch_traits.hpp>
#include <category/vm/evm/traits.hpp>
#include <category/vm/llvm/execute.hpp>
#include <category/vm/llvm/llvm.hpp>
#include <category/vm/runtime/transmute.hpp>
#include <category/vm/runtime/types.hpp>
#include <category/vm/utils/evmc_utils.hpp>

#include <evmc/evmc.h>
#include <evmc/evmc.hpp>

#include <cstddef>
#include <cstdint>
#include <cstdlib>
#include <filesystem>
#include <format>
#include <memory>
#include <span>
#include <string>
#include <unordered_map>
#include <vector>

namespace monad::vm::llvm
{
    std::vector<std::string> extensions(std::filesystem::path fn)
    {
        std::vector<std::string> exts;
        while (!fn.extension().empty()) {
            exts.insert(exts.begin(), fn.extension().string());
            fn = fn.stem();
        }
        return exts;
    }

    void VM::load_llvm_file_cache()
    {
        for (auto const &entry : std::filesystem::directory_iterator(
                 std::filesystem::current_path())) {
            std::filesystem::path const fn = entry.path().filename();
            std::vector<std::string> exts = extensions(fn);

            auto const file_cache_num_exts = 4;

            if (exts.size() == file_cache_num_exts && exts[2] == ".jit" &&
                exts[3] == ".o") {
                evmc_revision const rev =
                    static_cast<evmc_revision>(std::stoi(exts[0].substr(1)));
                uint256_t const hash256 =
                    runtime::uint256_t::from_string("0x" + exts[1].substr(1));

                evmc::bytes32 const code_hash = bytes32_from_uint256(hash256);

                std::shared_ptr<LLVMState> const ptr =
                    monad::vm::llvm::load_from_disk(rev, entry.path().string());

                cached_llvm_code_[rev].insert({code_hash, ptr});
            }
        }
    }

    VM::VM(std::size_t max_stack_cache)
        : stack_allocator_{max_stack_cache}
        , cached_llvm_code_(
              EVMC_MAX_REVISION + 1,
              std::unordered_map<evmc::bytes32, std::shared_ptr<LLVMState>>())
    {
        load_llvm_file_cache();
    }

    std::shared_ptr<LLVMState> VM::cache_llvm(
        evmc_revision rev, evmc::bytes32 const &code_hash, uint8_t const *code,
        size_t code_size)
    {
        auto const item = cached_llvm_code_[rev].find(code_hash);
        if (item != cached_llvm_code_[rev].end()) {
            return item->second;
        }

        auto const *isq = std::getenv("MONAD_VM_LLVM_DEBUG");
        auto code_hash_str = monad::vm::utils::hex_string(code_hash);
        std::string const hash_str =
            std::format(".{}.{}", (int)rev, code_hash_str);
        std::string const dbg_nm = isq ? "t" + hash_str : "";
        auto ptr = monad::vm::llvm::compile(rev, {code, code_size}, dbg_nm);

        cached_llvm_code_[rev].insert({code_hash, ptr});

        return ptr;
    }

    template <Traits traits>
    static evmc::Result copy_to_evmc_result_impl(runtime::Context &ctx)
    {
        auto result = ctx.copy_to_evmc_result<traits>();
        return result;
    }

    evmc::Result VM::execute_llvm(
        evmc_revision rev, evmc::bytes32 const &code_hash,
        runtime::Context &ctx, uint8_t const *code, size_t code_size)
    {

        auto const stack_ptr = stack_allocator_.allocate();
        uint256_t *evm_stack = reinterpret_cast<uint256_t *>(stack_ptr.get());

        auto const llvm = cache_llvm(rev, code_hash, code, code_size);

        monad::vm::llvm::execute(*llvm, ctx, evm_stack);

        SWITCH_EVM_TRAITS(copy_to_evmc_result_impl, ctx);

        std::unreachable();
    }

    void execute_compiled_llvm(
        std::shared_ptr<LLVMState> llvm, runtime::Context *ctx,
        uint8_t *evm_stack)
    {
        monad::vm::llvm::execute(
            *llvm, *ctx, reinterpret_cast<runtime::uint256_t *>(evm_stack));
    }

    template <Traits traits>
    std::shared_ptr<LLVMState> compile_basicblocks_llvm(
        compiler::basic_blocks::BasicBlocksIR const &ir,
        std::string const &dbg_nm)
    {
        return monad::vm::llvm::compile_basicblocks_impl<traits>(ir, dbg_nm);
    }

    EXPLICIT_TRAITS(compile_basicblocks_llvm);

}
