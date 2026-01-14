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

#include <category/vm/evm/traits.hpp>
#include <category/vm/llvm/dependency_blocks.hpp>
#include <category/vm/llvm/llvm_state.hpp>
#include <category/vm/runtime/call.hpp>
#include <category/vm/runtime/create.hpp>
#include <category/vm/runtime/data.hpp>
#include <category/vm/runtime/detail.hpp>
#include <category/vm/runtime/environment.hpp>
#include <category/vm/runtime/keccak.hpp>
#include <category/vm/runtime/log.hpp>
#include <category/vm/runtime/math.hpp>
#include <category/vm/runtime/memory.hpp>
#include <category/vm/runtime/selfdestruct.hpp>
#include <category/vm/runtime/storage.hpp>

#include <evmc/evmc.hpp>
#include <intx/intx.hpp>

namespace monad::vm::runtime
{

    inline void context_expand_memory(Context *ctx, Bin<29> min_size)
    {
        ctx->expand_memory(min_size);
    }

    inline void llvm_runtime_debug(
        Context *ctx, int64_t *gas_p, uint256_t *stack_begin,
        uint256_t *stack_top)
    {
        std::cerr << std::format("mem size: {}\n", ctx->memory.size);
        std::cerr << std::format("gas {}\n", *gas_p);
        std::cerr << std::format(
            "gas price {}\n",
            intx::hex(intx::be::load<intx::uint256>(
                ctx->env.tx_context->tx_gas_price)));
        std::cerr << std::format("stack:\n", *stack_begin);
        int i = 0;
        while (stack_begin < stack_top) {
            std::cerr << std::format("{}: {}\n", i, *stack_begin);
            stack_begin++;
            i++;
        }
    }

    inline void llvm_runtime_debug_pointer(void *p)
    {
        std::cerr << std::format("RUNTIME DEBUG pointer: {}\n", p);
    }

    inline void llvm_runtime_debug_string(char *s)
    {
        std::cerr << std::format("RUNTIME DEBUG string: {}\n", s);
    }

    inline void
    llvm_runtime_debug_word(uint64_t a, uint64_t b, uint64_t c, uint64_t d)
    {
        uint256_t x = d;
        x = (x << 64) | c;
        x = (x << 64) | b;
        x = (x << 64) | a;

        std::cerr << std::format("RUNTIME DEBUG i256: {}\n", x);
    }

    inline void llvm_runtime_debug_i32(uint32_t x)
    {
        std::cerr << std::format("RUNTIME DEBUG i32: {}\n", x);
    }

}

namespace monad::vm::llvm
{
    using namespace monad::vm::compiler;
    using namespace monad::vm::runtime;
    using namespace monad::vm::dependency_blocks;

    using enum Terminator;
    using enum OpCode;

    inline std::string instr_name(Instruction const &instr)
    {
        return std::format("{}", instr);
    }

    inline std::string term_name(Terminator term)
    {
        return std::format("{}", term);
    }

    struct OpDefnArgs
    {
        Value *ctx_ref;
        Value *gas_remaining;
        std::vector<Value *> var_args;
    };

    struct SaveInsert
    {
        explicit SaveInsert(LLVMState &llvm)
            : llvm(llvm)
        {
            llvm.save_insert();
        }

        ~SaveInsert()
        {
            llvm.restore_insert();
        }

    private:
        LLVMState &llvm;
    };

    template <Traits traits>
    struct Emitter
    {

    public:
        Emitter(LLVMState &llvm, DependencyBlocksIR &dep_ir)
            : llvm(llvm)
            , dep_ir(dep_ir)
        {
        }

        Value *EvmValue_to_value(EvmValue const &arg)
        {
            Value *val;
            std::visit<void>(
                Cases{
                    [&](uint256_t const &c) { val = llvm.lit_word(c); },
                    [&](InstrIdx const &j) { val = value_tbl[j]; },
                },
                arg);
            return val;
        }

        void prep_for_return(EvmValue const &a, EvmValue const &b)
        {
            auto *offsetp = context_gep(
                g_ctx_ref, context_offset_result_offset, "result_offset");
            llvm.store(EvmValue_to_value(a), offsetp);
            auto *sizep = context_gep(
                g_ctx_ref, context_offset_result_size, "result_size");
            llvm.store(EvmValue_to_value(b), sizep);
        }

        void selfdestruct_(EvmValue const &v)
        {
            if (selfdestruct_f == nullptr) {
                selfdestruct_f = declare_symbol(
                    term_name(SelfDestruct),
                    (void *)(&selfdestruct<traits>),
                    llvm.void_ty,
                    {llvm.ptr_ty(context_ty), llvm.ptr_ty(llvm.word_ty)});
            }

            auto *p = assign(EvmValue_to_value(v), "addr");
            llvm.call_void(selfdestruct_f, {g_ctx_ref, p});
            llvm.unreachable();
        };

        std::tuple<byte_offset, byte_offset, byte_offset> init_jumptable()
        {
            MONAD_VM_ASSERT(!jumpdest_tbl.empty());

            byte_offset min_offset = std::numeric_limits<byte_offset>::max();
            byte_offset max_offset = 0;

            for (auto const &[k, _] : jumpdest_tbl) {
                min_offset = std::min(min_offset, k);
                max_offset = std::max(max_offset, k);
            }

            byte_offset const err_offset = max_offset + 1;

            byte_offset const sz = use_small_jumptable
                                       ? err_offset - min_offset + 1
                                       : err_offset + 1;

            jumptable_ty = llvm.array_ty(block_addr_ty, sz);

            std::vector<Constant *> vals(sz);

            for (byte_offset i = 0; i < sz; ++i) {
                if (use_small_jumptable) {
                    vals[i] = llvm.block_address(lookup_jumpdest(
                        static_cast<uint256_t>(i + min_offset)));
                }
                else {
                    vals[i] = llvm.block_address(
                        lookup_jumpdest(static_cast<uint256_t>(i)));
                }
            }

            jumptable = llvm.const_array(vals, "jumptable");
            return {min_offset, max_offset, err_offset};
        }

        BasicBlock *lookup_jumpdest(uint256_t c)
        {
            if (c > std::numeric_limits<byte_offset>::max()) {
                return error_lbl();
            }

            auto const item = jumpdest_tbl.find(static_cast<byte_offset>(c));
            if (item == jumpdest_tbl.end()) {
                return error_lbl();
            }

            return item->second;
        }

        void emit_jump(EvmValue const &v)
        {
            std::visit<void>(
                Cases{
                    [&](uint256_t const &c) { llvm.br(lookup_jumpdest(c)); },

                    [&](InstrIdx const &i) { llvm.br(indirectbr_lbl(i)); },
                },
                v);
        }

        void emit_jumpi(
            EvmValue const &else_v, EvmValue const &pred, BasicBlock *then_lbl)
        {
            std::visit<void>(
                Cases{
                    [&](uint256_t const &c) {
                        if (c == 0) {
                            llvm.br(then_lbl);
                            return;
                        }
                        emit_jump(else_v);
                        return;
                    },
                    [&](InstrIdx const &i) {
                        auto *isz = llvm.eq(value_tbl[i], llvm.lit_word(0));

                        BasicBlock *else_lbl = std::visit(
                            Cases{
                                [&](uint256_t const &c) {
                                    return lookup_jumpdest(c);
                                },
                                [&](InstrIdx const &j) {
                                    return indirectbr_lbl(j);
                                },
                            },
                            else_v);

                        llvm.condbr(isz, then_lbl, else_lbl, false);
                    },
                },
                pred);
        }

        void terminate_block(
            Terminator term, std::vector<EvmValue> const &args,
            BasicBlock *fallthrough_lbl)
        {
            switch (term) {
            case Jump:
                emit_jump(args[0]);
                return;
            case JumpI:
                emit_jumpi(args[0], args[1], fallthrough_lbl);
                return;
            case FallThrough:
                llvm.br(fallthrough_lbl);
                return;
            case Stop:
                llvm.br(return_lbl());
                return;
            case Return:
                prep_for_return(args[0], args[1]);
                llvm.br(return_lbl());
                return;
            case Revert:
                prep_for_return(args[0], args[1]);
                llvm.br(revert_lbl());
                return;
            case SelfDestruct:
                selfdestruct_(args[0]);
                return;
            default:
                MONAD_VM_ASSERT(term == InvalidInstruction);
                llvm.br(error_lbl());
                return;
            };
        };

        void insert_value(InstrIdx i, Value *v)
        {
            if (static_cast<InstrIdx>(value_tbl.size()) <= i) {
                value_tbl.resize(i + 1);
            }
            value_tbl[i] = v;
        }

        Value *stacktop_offset(Value *stack_top, StackIdx i)
        {
            return llvm.gep(
                llvm.word_ty, stack_top, {llvm.i32(i)}, "stacktop_offset");
        }

        Value *check_and_update_gas(int64_t const blk_gas_update)
        {
            if (blk_gas_update == 0) {
                return llvm.bool_(false);
            }

            if (check_and_update_gas_f == nullptr) {
                SaveInsert const _unused(llvm);
                auto [f, arg] = llvm.internal_function_definition(
                    "check_and_update_gas",
                    llvm.bool_ty,
                    {llvm.ptr_ty(llvm.int_ty(64)), llvm.int_ty(64)});
                check_and_update_gas_f = f;
                auto *entry = llvm.basic_block("entry", f);
                llvm.insert_at(entry);

                Value *gas_ref = arg[0];
                gas_ref->setName("gas_ref");
                Value *blk_gas_update = arg[1];
                blk_gas_update->setName("blk_gas_update");

                auto *gas = llvm.load(llvm.int_ty(64), gas_ref);
                auto *gas1 = llvm.sub(gas, blk_gas_update);
                llvm.store(gas1, gas_ref);
                auto *gas_lt_zero = llvm.slt(gas1, llvm.i64(0));
                llvm.ret(gas_lt_zero);
            }

            return llvm.call(
                check_and_update_gas_f,
                {g_ctx_gas_ref, llvm.i64(blk_gas_update)},
                "is_gas_ok");
        }

        void emit_block_check(Value *is_err)
        {
            if (block_check_f == nullptr) {
                SaveInsert const _unused(llvm);
                auto [f, arg] = llvm.internal_function_definition(
                    "block_check",
                    llvm.void_ty,
                    {llvm.ptr_ty(context_ty), llvm.bool_ty});
                block_check_f = f;
                auto *entry = llvm.basic_block("entry", f);
                auto *ok_lbl = llvm.basic_block("ok_lbl", f);
                auto *err_lbl = llvm.basic_block("err_lbl", f);

                Value *ctx_ref = arg[0];
                ctx_ref->setName("ctx_ref");
                f->addParamAttr(0, Attribute::NoAlias);
                Value *is_err_v = arg[1];
                is_err_v->setName("is_err");

                llvm.insert_at(entry);
                llvm.condbr(is_err_v, err_lbl, ok_lbl, false);

                llvm.insert_at(err_lbl);
                exit_(ctx_ref, StatusCode::Error);

                llvm.insert_at(ok_lbl);
                llvm.ret_void();
            }

            llvm.call_void(block_check_f, {g_ctx_ref, is_err});
        }

        void emit_contract()
        {
            contract_start();

            for (auto const &[offset, _] : dep_ir.jump_dests) {
                jumpdest_tbl.insert({offset, get_block_lbl(offset)});
            }

            for (DependencyBlock const &blk : dep_ir.blocks) {
                auto *lbl = get_block_lbl(blk.offset);
                llvm.insert_at(lbl);

                Value *stack_top = load_stack_top_p();

                Value *is_neg = check_and_update_gas(blk.block_gas_update);
                Value *is_under = is_stack_underflow(stack_top, blk.low);
                Value *is_over = is_stack_overflow(stack_top, blk.high);

                Value *is_any = llvm.or_(llvm.or_(is_neg, is_under), is_over);

                emit_block_check(is_any);

                for (auto const &item : blk.instrs) {
                    auto i = std::get<0>(item);
                    auto instr = std::get<1>(item);

                    std::visit<void>(
                        Cases{
                            [&](struct EvmInstr const &ei) {
                                emit_instr(blk.offset, i, ei);
                            },
                            [&](struct UnspillInstr const &ui) {
                                Value *v = llvm.load(
                                    llvm.word_ty,
                                    stacktop_offset(stack_top, ui.idx));
                                insert_value(i, v);
                            },
                            [&](struct SpillInstr const &si) {
                                llvm.store(
                                    EvmValue_to_value(si.val),
                                    stacktop_offset(stack_top, si.idx));
                            },
                        },
                        instr);
                }

                switch (blk.terminator) {
                case Jump:
                case JumpI:
                case FallThrough:
                    store_stack_top_p(stacktop_offset(stack_top, blk.delta));
                    break;
                default:
                    break;
                }

                BasicBlock *fallthrough_lbl =
                    blk.fallthrough_dest == INVALID_BLOCK_ID
                        ? error_lbl()
                        : get_block_lbl(
                              dep_ir.blocks[blk.fallthrough_dest].offset);
                terminate_block(
                    blk.terminator, blk.terminator_args, fallthrough_lbl);
            }
            contract_finish();
        }

    private:
        LLVMState &llvm;
        DependencyBlocksIR &dep_ir;

        Value *g_ctx_ref = nullptr;
        Value *g_ctx_gas_ref = nullptr;

        // cached for use with memory opcodes
        Value *g_cached_mem_size_ptr = nullptr;
        Value *g_cached_mem_data_ptr_ptr = nullptr;

        Value *evm_stack_begin = nullptr;
        Value *evm_stack_end = nullptr;
        Value *evm_stack_top_p = nullptr;

        Value *jumptable = nullptr;
        Type *block_addr_ty = llvm.ptr_ty(llvm.int_ty(8));
        Type *jumptable_ty;

        std::unordered_map<std::string, Function *> llvm_opcode_tbl;
        // ^ string instead of opcode for Log

        std::unordered_map<byte_offset, BasicBlock *> block_tbl;
        std::unordered_map<byte_offset, BasicBlock *> jumpdest_tbl;

        Type *context_ty = llvm.void_ty;
        Type *evmc_tx_context_ty = llvm.void_ty;

        Function *exit_f = init_exit();
        Function *llvm_runtime_debug_f = nullptr;
        Function *llvm_runtime_debug_word_f = nullptr;
        Function *llvm_runtime_debug_pointer_f = nullptr;
        Function *llvm_runtime_debug_string_f = nullptr;
        Function *llvm_runtime_debug_i32_f = nullptr;
        Function *context_expand_memory_f = nullptr;
        Function *selfdestruct_f = nullptr;
        Function *check_and_update_gas_f = nullptr;
        Function *is_stack_underflow_f = nullptr;
        Function *is_stack_overflow_f = nullptr;
        Function *block_check_f = nullptr;

        BasicBlock *error_lbl_v = nullptr;
        BasicBlock *return_lbl_v = nullptr;
        BasicBlock *revert_lbl_v = nullptr;

        BasicBlock *indirectbr_lbl_v = nullptr;
        PHINode *indirectbr_phi = nullptr;

        std::vector<Value *> value_tbl;

        BasicBlock *entry = nullptr;
        Function *contract = nullptr;

        char const *use_alloca_stack =
            std::getenv("MONAD_VM_LLVM_ALLOCA_STACK");
        char const *use_small_jumptable =
            std::getenv("MONAD_VM_LLVM_USE_SMALL_JUMPTABLE");
        char const *output_llvm_debug_prints =
            std::getenv("MONAD_VM_LLVM_RUNTIME_DEBUG_PRINTS");

        void copy_gas(Value *from, Value *to)
        {
            auto *gas = llvm.load(llvm.int_ty(64), from);
            llvm.store(gas, to);
        }

        void store_stack_top_p(Value *stack_top)
        {
            llvm.store(stack_top, evm_stack_top_p);
        }

        Value *load_stack_top_p()
        {
            return llvm.load(llvm.ptr_ty(llvm.word_ty), evm_stack_top_p);
        }

        BasicBlock *error_lbl()
        {
            if (error_lbl_v == nullptr) {
                SaveInsert const _unused(llvm);
                error_lbl_v = llvm.basic_block("error_lbl", contract);
                llvm.insert_at(error_lbl_v);
                exit_(g_ctx_ref, StatusCode::Error);
            }
            return error_lbl_v;
        }

        BasicBlock *return_lbl()
        {
            if (return_lbl_v == nullptr) {
                SaveInsert const _unused(llvm);
                return_lbl_v = llvm.basic_block("return_lbl", contract);
                llvm.insert_at(return_lbl_v);
                exit_(g_ctx_ref, StatusCode::Success);
            }
            return return_lbl_v;
        }

        BasicBlock *revert_lbl()
        {
            if (revert_lbl_v == nullptr) {
                SaveInsert const _unused(llvm);
                revert_lbl_v = llvm.basic_block("revert_lbl", contract);
                llvm.insert_at(revert_lbl_v);
                exit_(g_ctx_ref, StatusCode::Revert);
            }
            return revert_lbl_v;
        }

        BasicBlock *indirectbr_lbl(InstrIdx i)
        {
            if (jumpdest_tbl.empty()) {
                return error_lbl();
            }

            if (indirectbr_lbl_v == nullptr) {
                auto const &[min_offset, max_offset, err_offset] =
                    init_jumptable();

                indirectbr_lbl_v = llvm.basic_block("indirectbr_lbl", contract);
                SaveInsert const _unused(llvm);
                llvm.insert_at(indirectbr_lbl_v);

                indirectbr_phi = llvm.phi(llvm.word_ty);

                Value *is_lte_max_offset = llvm.ule(
                    indirectbr_phi,
                    llvm.lit_word(static_cast<uint256_t>(err_offset)));

                Value *lte_offset = llvm.select(
                    is_lte_max_offset,
                    llvm.cast_64(indirectbr_phi),
                    llvm.u64(err_offset));
                Value *sub_offset;
                if (use_small_jumptable) {
                    Value *is_gte_min_offset =
                        llvm.uge(lte_offset, llvm.u64(min_offset));

                    Value *gte_offset = llvm.select(
                        is_gte_min_offset, lte_offset, llvm.u64(err_offset));

                    sub_offset = llvm.sub(gte_offset, llvm.u64(min_offset));
                    // you can eliminate this subtraction by rewriting the
                    // jumptable address
                }
                else {
                    sub_offset = lte_offset;
                }

                Value *p = llvm.gep(
                    jumptable_ty,
                    jumptable,
                    {llvm.u32(0), sub_offset},
                    "jumpdest_p");

                Value *jd_addr = llvm.load(llvm.ptr_ty(block_addr_ty), p);
                IndirectBrInst *indirectbr_v = llvm.indirectbr(jd_addr);

                llvm.indirect_br_add_dest(indirectbr_v, error_lbl());
                for (auto const &[_, lbl] : jumpdest_tbl) {
                    llvm.indirect_br_add_dest(indirectbr_v, lbl);
                }
            }

            llvm.phi_add_incoming(
                indirectbr_phi, value_tbl[i], llvm.get_insert());

            return indirectbr_lbl_v;
        }

        Value *get_ctx_mem_data_ptr(Value *ctx_ref)
        {
            auto *ctx_mem_data_ptr_ptr = context_gep(
                ctx_ref, context_offset_memory_data, "ctx_mem_data_ptr_ptr");
            return llvm.load(llvm.ptr_ty(llvm.int_ty(8)), ctx_mem_data_ptr_ptr);
        }

        void update_memory_refs(
            Value *ctx_ref, Value *mem_size_ptr, Value *mem_data_ptr_ptr)
        {
            auto *ctx_mem_size_ptr = context_gep(
                ctx_ref, context_offset_memory_size, "ctx_mem_size_ptr");

            auto *ctx_mem_size = llvm.load(llvm.int_ty(32), ctx_mem_size_ptr);
            llvm.store(ctx_mem_size, mem_size_ptr);

            auto *ctx_mem_data_ptr = get_ctx_mem_data_ptr(ctx_ref);
            llvm.store(ctx_mem_data_ptr, mem_data_ptr_ptr);
        }

        void contract_start()
        {
            auto [contractf, arg] = llvm.external_function_definition(
                "contract",
                llvm.void_ty,
                {llvm.ptr_ty(llvm.word_ty), llvm.ptr_ty(context_ty)});

            contract = contractf;
            contract->addFnAttr(Attribute::NoReturn);
            contract->addParamAttr(0, Attribute::NoAlias);
            contract->addParamAttr(1, Attribute::NoAlias);

            entry = llvm.basic_block("entry", contract);

            llvm.insert_at(entry);

            if (use_alloca_stack) {
                ArrayType *stack_ty = llvm.array_ty(llvm.word_ty, 1024);
                evm_stack_begin = llvm.alloca_(stack_ty, "evm_stack_begin");
            }
            else {
                evm_stack_begin = arg[0];
                evm_stack_begin->setName("evm_stack_begin");
            }
            g_ctx_ref = arg[1];
            g_ctx_ref->setName("ctx_ref");

            g_ctx_gas_ref = context_gep(
                g_ctx_ref, context_offset_gas_remaining, "ctx_gas_ref");

            g_cached_mem_size_ptr =
                llvm.alloca_(llvm.int_ty(32), "mem_size_ptr");
            g_cached_mem_data_ptr_ptr =
                llvm.alloca_(llvm.ptr_ty(llvm.int_ty(8)), "mem_data_ptr_ptr");

            update_memory_refs(
                g_ctx_ref, g_cached_mem_size_ptr, g_cached_mem_data_ptr_ptr);

            evm_stack_end = llvm.gep(
                llvm.word_ty,
                evm_stack_begin,
                {llvm.u64(1024)},
                "evm_stack_end");

            evm_stack_top_p =
                llvm.alloca_(llvm.ptr_ty(llvm.word_ty), "evm_stack_top_p");

            store_stack_top_p(evm_stack_begin);
        }

        Value *evm_stack_idx(Value *stack_top, int64_t i)
        {
            return llvm.gep(
                llvm.word_ty, stack_top, {llvm.i64(i)}, "evm_stack_idx");
        };

        void contract_finish()
        {
            llvm.insert_at(entry);
            MONAD_VM_ASSERT(!dep_ir.blocks.empty());
            llvm.br(get_block_lbl(dep_ir.blocks.front().offset));
        };

        std::string to_register_name(byte_offset blkId, InstrIdx i)
        {
            return std::format("v{}_{}", blkId, i);
        }

        void emit_llvm_runtime_debug_string(std::string const &s)
        {
            if (output_llvm_debug_prints) {
                if (llvm_runtime_debug_string_f == nullptr) {
                    llvm_runtime_debug_string_f = declare_symbol(
                        "llvm_runtime_debug_string",
                        (void *)(llvm_runtime_debug_string),
                        llvm.void_ty,
                        {llvm.ptr_ty(llvm.int_ty(8))});
                }
                llvm.call_void(
                    llvm_runtime_debug_string_f, {llvm.lit_string(s)});
            }
        }

        void emit_llvm_runtime_debug_pointer(Value *v)
        {
            if (output_llvm_debug_prints) {
                if (llvm_runtime_debug_pointer_f == nullptr) {
                    llvm_runtime_debug_pointer_f = declare_symbol(
                        "llvm_runtime_debug_pointer",
                        (void *)(llvm_runtime_debug_pointer),
                        llvm.void_ty,
                        {llvm.ptr_ty(llvm.int_ty(8))});
                }
                llvm.call_void(llvm_runtime_debug_pointer_f, {v});
            }
        }

        void emit_llvm_runtime_debug_i32(Value *v)
        {
            if (output_llvm_debug_prints) {
                if (llvm_runtime_debug_i32_f == nullptr) {
                    llvm_runtime_debug_i32_f = declare_symbol(
                        "llvm_runtime_debug_i32",
                        (void *)(llvm_runtime_debug_i32),
                        llvm.void_ty,
                        {llvm.int_ty(32)});
                }
                llvm.call_void(llvm_runtime_debug_i32_f, {v});
            }
        }

        void emit_llvm_runtime_debug_word(Value *v)
        {
            if (output_llvm_debug_prints) {
                if (llvm_runtime_debug_word_f == nullptr) {
                    llvm_runtime_debug_word_f = declare_symbol(
                        "llvm_runtime_debug_word",
                        (void *)(llvm_runtime_debug_word),
                        llvm.void_ty,
                        {llvm.word_ty});
                }

                llvm.call_void(llvm_runtime_debug_word_f, {v});
            }
        }

        void emit_llvm_runtime_debug()
        {
            if (output_llvm_debug_prints) {
                if (llvm_runtime_debug_f == nullptr) {
                    auto f = declare_symbol(
                        "llvm_runtime_debug",
                        (void *)(llvm_runtime_debug),
                        llvm.void_ty,
                        {llvm.ptr_ty(context_ty),
                         llvm.ptr_ty(llvm.int_ty(64)),
                         llvm.ptr_ty(llvm.word_ty),
                         llvm.ptr_ty(llvm.word_ty)});
                    llvm_runtime_debug_f = f;
                }
                Value *stack_top = load_stack_top_p();
                llvm.call_void(
                    llvm_runtime_debug_f,
                    {g_ctx_ref, g_ctx_gas_ref, evm_stack_begin, stack_top});
            }
        }

        void emit_instr(
            byte_offset blkId, InstrIdx const &i, struct EvmInstr const &ei)
        {
            Function *f;
            auto const nm = instr_name(ei.instr);

            auto const item = llvm_opcode_tbl.find(nm);
            if (item != llvm_opcode_tbl.end()) {
                f = item->second;
            }
            else {
                f = init_instr(ei.instr);
                llvm_opcode_tbl.insert({nm, f});
            }

            std::vector<Value *> args;

            args.push_back(g_ctx_ref);

            auto *g = llvm.i64(ei.remaining_block_base_gas);
            args.push_back(g);

            if (ei.instr.opcode() == Gas) {
                args.push_back(g_ctx_gas_ref);
            }

            if (ei.instr.opcode() == MLoad || ei.instr.opcode() == MStore ||
                ei.instr.opcode() == MStore8) {
                args.push_back(g_cached_mem_size_ptr);
                args.push_back(g_cached_mem_data_ptr_ptr);
            }

            for (auto const &arg : ei.args) {
                args.push_back(EvmValue_to_value(arg));
            }

            if (ei.instr.increases_stack()) {
                auto v = llvm.call(f, args, to_register_name(blkId, i));
                insert_value(i, v);
            }
            else {
                llvm.call_void(f, args);
            }
            if (ei.instr.opcode() == CallCode || ei.instr.opcode() == Call ||
                ei.instr.opcode() == DelegateCall ||
                ei.instr.opcode() == StaticCall ||
                ei.instr.opcode() == Create || ei.instr.opcode() == Create2 ||
                ei.instr.opcode() == ExtCodeCopy ||
                ei.instr.opcode() == ReturnDataCopy ||
                ei.instr.opcode() == CallDataCopy ||
                ei.instr.opcode() == CodeCopy || ei.instr.opcode() == Sha3 ||
                ei.instr.opcode() == Log || ei.instr.opcode() == MCopy) {
                update_memory_refs(
                    g_ctx_ref,
                    g_cached_mem_size_ptr,
                    g_cached_mem_data_ptr_ptr);
            }
        };

        Function *init_exit()
        {
            auto [f, _arg] = llvm.external_function_definition(
                "rt_EXIT",
                llvm.void_ty,
                {llvm.ptr_ty(context_ty), llvm.int_ty(64)});
            f->addFnAttr(Attribute::NoReturn);
            return f;
        }

        void exit_(Value *ctx_ref, StatusCode status)
        {
            llvm.call_void(
                exit_f, {ctx_ref, llvm.u64(static_cast<uint64_t>(status))});
            llvm.unreachable();
        }

        Value *is_stack_overflow(Value *stack_top, int32_t high)
        {
            if (high <= 0) {
                return llvm.bool_(false);
            }

            if (is_stack_overflow_f == nullptr) {
                SaveInsert const _unused(llvm);
                auto [f, arg] = llvm.internal_function_definition(
                    "is_stack_overflow",
                    llvm.bool_ty,
                    {llvm.ptr_ty(llvm.word_ty), llvm.ptr_ty(llvm.word_ty)});

                is_stack_overflow_f = f;
                auto *entry = llvm.basic_block("entry", f);

                llvm.insert_at(entry);

                Value *stack_end = arg[0];
                stack_end->setName("stack_end");
                Value *stack_high = arg[1];
                stack_high->setName("stack_high");

                auto *is_stack_err = llvm.sgt(stack_high, stack_end);
                llvm.ret(is_stack_err);
            }

            return llvm.call(
                is_stack_overflow_f,
                {evm_stack_end, stacktop_offset(stack_top, high)},
                "is_stack_overflow");
        };

        Value *is_stack_underflow(Value *stack_top, int32_t low)
        {
            if (low >= 0) {
                return llvm.bool_(false);
            }

            if (is_stack_underflow_f == nullptr) {
                SaveInsert const _unused(llvm);
                auto [f, arg] = llvm.internal_function_definition(
                    "is_stack_underflow",
                    llvm.bool_ty,
                    {llvm.ptr_ty(llvm.word_ty), llvm.ptr_ty(llvm.word_ty)});

                is_stack_underflow_f = f;
                auto *entry = llvm.basic_block("entry", f);
                llvm.insert_at(entry);

                Value *stack_begin = arg[0];
                stack_begin->setName("stack_begin");
                Value *stack_low = arg[1];
                stack_low->setName("stack_low");

                auto *is_stack_err = llvm.slt(stack_low, stack_begin);
                llvm.ret(is_stack_err);
            }

            return llvm.call(
                is_stack_underflow_f,
                {evm_stack_begin, stacktop_offset(stack_top, low)},
                "is_stack_underflow");
        };

        BasicBlock *get_block_lbl(byte_offset offset)
        {
            auto const item = block_tbl.find(offset);
            if (item == block_tbl.end()) {
                auto const *nm =
                    dep_ir.is_jumpdest(offset) ? "jd" : "fallthrough";
                auto *lbl = llvm.basic_block(
                    std::format("{}_lbl_{}", nm, offset), contract);
                block_tbl.insert({offset, lbl});
                return lbl;
            }
            return item->second;
        };

        Value *context_gep(Value *ctx_ref, uint64_t offset, std::string_view nm)
        {
            return llvm.gep(llvm.int_ty(8), ctx_ref, {llvm.u64(offset)}, nm);
        };

        Value *assign(Value *v, std::string_view nm)
        {
            Value *p = llvm.alloca_(llvm.word_ty, nm);
            llvm.store(v, p);
            return p;
        }

        Function *declare_symbol(
            std::string_view nm0, void *f, Type *ty,
            std::vector<Type *> const &tys)
        {
            std::string const nm = "ffi_" + std::string(nm0);
            llvm.insert_symbol(nm, f);
            return llvm.declare_function(nm, ty, tys, true);
        };

        template <typename... FnArgs>
        Function *ffi_runtime(Instruction const &instr, void (*fun)(FnArgs...))
        {
            SaveInsert const _unused(llvm);

            constexpr auto has_ctx = detail::uses_context_v<FnArgs...>;
            constexpr auto has_gas = detail::uses_remaining_gas_v<FnArgs...>;
            bool const has_ret = instr.increases_stack();
            size_t const n = instr.stack_args();
            std::string const nm = instr_name(instr);

            std::vector<Type *> tys;
            std::vector<Type *> ffi_tys;

            tys.push_back(
                llvm.ptr_ty(context_ty)); // first param always context
            tys.push_back(
                llvm.int_ty(64)); // second param always block gas remaining

            if (has_ctx) {
                ffi_tys.push_back(llvm.ptr_ty(context_ty));
            }

            if (has_ret) {
                ffi_tys.push_back(llvm.ptr_ty(llvm.word_ty)); // result
            }

            for (size_t i = 0; i < n; ++i) {
                tys.push_back(llvm.word_ty);
                ffi_tys.push_back(llvm.ptr_ty(llvm.word_ty));
            }

            if (has_gas) {
                ffi_tys.push_back(llvm.int_ty(64));
            }

            auto *ffi = declare_symbol(nm, (void *)fun, llvm.void_ty, ffi_tys);

            auto [f, arg] = llvm.internal_function_definition(
                nm, has_ret ? llvm.word_ty : llvm.void_ty, tys);

            arg[0]->setName("evm_ctx");
            f->addParamAttr(0, Attribute::NoAlias);

            arg[1]->setName("gas");

            for (size_t i = 2; i < arg.size(); ++i) {
                arg[i]->setName(std::format("arg{}", i));
            }
            auto *entry = llvm.basic_block("entry", f);
            llvm.insert_at(entry);

            std::vector<Value *> vals;

            if (has_ctx) {
                vals.push_back(arg[0]);
            }

            for (size_t i = 0; i < n; ++i) {
                auto *p = assign(
                    arg[i + 2], "arg"); // uint256 values start at index 2
                vals.push_back(p);
            }

            Value *r = nullptr;

            long const di = has_ctx ? 1 : 0;

            if (has_ret) {
                r = n == 0 ? llvm.alloca_(llvm.word_ty, "retval") : vals[1];
                vals.insert(vals.begin() + di, r);
            }

            if (has_gas) {
                vals.push_back(arg[1]);
            }

            llvm.call_void(ffi, vals);

            if (has_ret) {
                llvm.ret(llvm.load(llvm.word_ty, r));
            }
            else {
                llvm.ret_void();
            }

            return f;
        };

        std::tuple<Function *, OpDefnArgs const>
        internal_op_definition(Instruction const &instr, int n)
        {
            std::vector<Type *> tys;
            tys.push_back(llvm.ptr_ty(context_ty));
            tys.push_back(llvm.int_ty(64));
            for (auto i = 0; i < n; ++i) {
                tys.push_back(llvm.word_ty);
            }
            auto [f, arg] = llvm.internal_function_definition(
                instr_name(instr), llvm.word_ty, tys);

            auto *a = arg[0];
            a->setName("evm_ctx");
            f->addParamAttr(0, Attribute::NoAlias);

            auto *b = arg[1];
            b->setName("gas");
            arg.erase(arg.begin(), arg.begin() + 2);

            OpDefnArgs const args = {a, b, arg};

            return std::make_tuple(f, args);
        }

        std::tuple<Function *, Value *> context_fun(Instruction const &instr)
        {
            auto [f, args] = internal_op_definition(instr, 0);
            auto *entry = llvm.basic_block("entry", f);
            llvm.insert_at(entry);
            return std::make_tuple(f, args.ctx_ref);
        };

        Function *load_context_addr(Instruction const &instr, uint64_t offset)
        {
            SaveInsert const _unused(llvm);

            auto [f, vctx] = context_fun(instr);
            auto *ref = context_gep(vctx, offset, "context_addr");
            auto *val = llvm.load(llvm.addr_ty, ref);
            llvm.ret(llvm.addr_to_word(val));
            return f;
        };

        Function *
        load_evmc_tx_context_addr(Instruction const &instr, uint64_t offset)
        {
            SaveInsert const _unused(llvm);

            auto [f, vctx] = context_fun(instr);

            // dereference the evmc_tx_context ptr
            auto *ptr_ref = context_gep(
                vctx,
                context_offset_env_tx_context,
                "context_offset_env_tx_context");
            auto *ptr_val = llvm.load(llvm.ptr_ty(evmc_tx_context_ty), ptr_ref);

            auto *ref = context_gep(ptr_val, offset, "evmc_tx_context_addr");
            auto *val = llvm.load(llvm.addr_ty, ref);

            llvm.ret(llvm.addr_to_word(val));
            return f;
        };

        Function *load_context_uint32(Instruction const &instr, uint64_t offset)
        {
            SaveInsert const _unused(llvm);

            auto [f, vctx] = context_fun(instr);
            auto *ref = context_gep(vctx, offset, "context_u32");
            auto *val = llvm.load(llvm.int_ty(32), ref);
            llvm.ret(llvm.cast_word(val));
            return f;
        };

        Function *load_context_uint64(Instruction const &instr, uint64_t offset)
        {
            SaveInsert const _unused(llvm);

            auto [f, vctx] = context_fun(instr);
            auto *ref = context_gep(vctx, offset, "context_u64");
            auto *val = llvm.load(llvm.int_ty(64), ref);
            llvm.ret(llvm.cast_word(val));
            return f;
        };

        Function *
        load_evmc_tx_context_uint64(Instruction const &instr, uint64_t offset)
        {
            SaveInsert const _unused(llvm);

            auto [f, vctx] = context_fun(instr);
            auto *ptr_ref = context_gep(
                vctx,
                context_offset_env_tx_context,
                "context_offset_env_tx_context");
            auto *ptr_val = llvm.load(llvm.ptr_ty(evmc_tx_context_ty), ptr_ref);

            auto *ref = context_gep(ptr_val, offset, "evmc_tx_context_u64");
            auto *val = llvm.load(llvm.int_ty(64), ref);
            llvm.ret(llvm.cast_word(val));
            return f;
        };

        Function *load_context_be(Instruction const &instr, uint64_t offset)
        {
            SaveInsert const _unused(llvm);

            auto [f, vctx] = context_fun(instr);
            auto *ref = context_gep(vctx, offset, "context_be");
            auto *val = llvm.load(llvm.word_ty, ref);
            llvm.ret(llvm.bswap(val));
            return f;
        };

        Function *
        load_evmc_tx_context_be(Instruction const &instr, uint64_t offset)
        {
            SaveInsert const _unused(llvm);

            auto [f, vctx] = context_fun(instr);
            auto *ptr_ref = context_gep(
                vctx,
                context_offset_env_tx_context,
                "context_offset_env_tx_context");
            auto *ptr_val = llvm.load(llvm.ptr_ty(evmc_tx_context_ty), ptr_ref);

            auto *ref = context_gep(ptr_val, offset, "evmc_tx_context_be");
            auto *val = llvm.load(llvm.word_ty, ref);
            llvm.ret(llvm.bswap(val));
            return f;
        };

        Function *llvm_unop(
            Instruction const &instr, Value *(LLVMState::*method)(Value *))
        {
            SaveInsert const _unused(llvm);

            auto [f, args] = internal_op_definition(instr, 1);
            auto *entry = llvm.basic_block("entry", f);
            llvm.insert_at(entry);
            llvm.ret((&llvm->*method)(args.var_args[0]));
            return f;
        }

        Function *llvm_binop(
            Instruction const &instr,
            Value *(LLVMState::*method)(Value *, Value *))
        {
            SaveInsert const _unused(llvm);

            auto [f, args] = internal_op_definition(instr, 2);
            auto *a = args.var_args[0];
            a->setName("a");
            auto *b = args.var_args[1];
            b->setName("b");
            auto *entry = llvm.basic_block("entry", f);
            llvm.insert_at(entry);
            llvm.ret(llvm.cast_word((&llvm->*method)(a, b)));
            return f;
        }

        Function *llvm_modop(
            Instruction const &instr,
            Value *(LLVMState::*method)(Value *, Value *, Value *))
        {
            SaveInsert const _unused(llvm);

            auto [f, args] = internal_op_definition(instr, 3);

            auto *a = args.var_args[0];
            auto *b = args.var_args[1];
            auto *n = args.var_args[2];

            auto *entry = llvm.basic_block("entry", f);
            auto *denom_is_0 = llvm.basic_block("denom_is_0", f);
            auto *denom_not_0 = llvm.basic_block("denom_not_0", f);

            llvm.insert_at(entry);
            llvm.condbr(
                llvm.eq(n, llvm.lit_word(0)), denom_is_0, denom_not_0, false);

            llvm.insert_at(denom_is_0);
            llvm.ret(llvm.lit_word(0));

            llvm.insert_at(denom_not_0);
            llvm.ret(llvm.cast_word((&llvm->*method)(a, b, n)));

            return f;
        }

        // needed for sdiv overflow semantics (minBound / -1)
        Function *llvm_sdivop(Instruction const &instr)
        {
            SaveInsert const _unused(llvm);

            auto [f, args] = internal_op_definition(instr, 2);
            Value *numer = args.var_args[0];
            Value *denom = args.var_args[1];

            auto *zero = llvm.lit_word(0);
            auto *neg1 = llvm.lit_word(
                0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff_u256);
            auto *minbound = llvm.lit_word(
                0x8000000000000000000000000000000000000000000000000000000000000000_u256);

            auto *entry = llvm.basic_block("entry", f);
            auto *ret_zero = llvm.basic_block("ret_zero", f);
            auto *ret_overflow = llvm.basic_block("ret_overflow", f);
            auto *ret_sdiv = llvm.basic_block("ret_sdiv", f);
            auto *try_denominator_neg1 =
                llvm.basic_block("try_denominator_neg1", f);
            auto *try_overflow_semantics =
                llvm.basic_block("try_overflow_semantics", f);

            llvm.insert_at(ret_zero);
            llvm.ret(zero);

            llvm.insert_at(ret_overflow);
            llvm.ret(minbound);

            llvm.insert_at(ret_sdiv);
            llvm.ret(llvm.sdiv(numer, denom));

            llvm.insert_at(entry); // check for denominator is 0
            llvm.condbr(
                llvm.eq(denom, zero), ret_zero, try_denominator_neg1, false);

            llvm.insert_at(try_denominator_neg1); // check for denominator is -1
            llvm.condbr(
                llvm.eq(denom, neg1), try_overflow_semantics, ret_sdiv, false);

            llvm.insert_at(
                try_overflow_semantics); // check for numerator is minbound
            llvm.condbr(
                llvm.eq(numer, minbound), ret_overflow, ret_sdiv, false);

            return f;
        }

        Function *llvm_divop(
            Instruction const &instr,
            Value *(LLVMState::*method)(Value *, Value *))
        {
            SaveInsert const _unused(llvm);

            auto [f, args] = internal_op_definition(instr, 2);
            Value *numer = args.var_args[0];
            numer->setName("numer");
            Value *denom = args.var_args[1];
            denom->setName("denom");
            auto *entry = llvm.basic_block("entry", f);
            llvm.insert_at(entry);

            auto *isz = llvm.eq(denom, llvm.lit_word(0));
            auto *then_lbl = llvm.basic_block("then_lbl", f);
            auto *else_lbl = llvm.basic_block("else_lbl", f);

            llvm.condbr(isz, then_lbl, else_lbl, false);

            llvm.insert_at(then_lbl);
            llvm.ret(llvm.lit_word(0));

            llvm.insert_at(else_lbl);
            llvm.ret((&llvm->*method)(numer, denom));

            return f;
        }

        Function *llvm_shiftop(
            Instruction const &instr,
            Value *(LLVMState::*method)(Value *, Value *))
        {
            SaveInsert const _unused(llvm);

            auto [f, args] = internal_op_definition(instr, 2);
            auto *entry = llvm.basic_block("entry", f);
            llvm.insert_at(entry);

            auto *a = args.var_args[0];
            a->setName("a");
            auto *b = args.var_args[1];
            b->setName("b");

            auto *isgt = llvm.ugt(a, llvm.lit_word(255));
            auto *then_lbl = llvm.basic_block("then_lbl", f);
            auto *else_lbl = llvm.basic_block("else_lbl", f);

            llvm.condbr(isgt, then_lbl, else_lbl, false);

            llvm.insert_at(then_lbl);
            llvm.ret(llvm.lit_word(0));

            llvm.insert_at(else_lbl);
            llvm.ret((&llvm->*method)(b, a));

            return f;
        }

        Function *llvm_byte(Instruction const &instr)
        {
            SaveInsert const _unused(llvm);

            auto [f, args] = internal_op_definition(instr, 2);

            auto *a = args.var_args[0];
            auto *b = args.var_args[1];

            auto *entry = llvm.basic_block("entry", f);
            llvm.insert_at(entry);

            auto *isgt = llvm.ugt(a, llvm.lit_word(31));
            auto *then_lbl = llvm.basic_block("then_lbl", f);
            auto *else_lbl = llvm.basic_block("else_lbl", f);

            llvm.condbr(isgt, then_lbl, else_lbl, false);

            llvm.insert_at(then_lbl);
            llvm.ret(llvm.lit_word(0));

            llvm.insert_at(else_lbl);

            auto *nbytes = llvm.sub(llvm.lit_word(31), a);
            auto *nbits = llvm.mul(nbytes, llvm.lit_word(8));
            llvm.ret(llvm.and_(llvm.shr(b, nbits), llvm.lit_word(255)));
            return f;
        }

        Function *llvm_gas(Instruction const &instr)
        {
            SaveInsert const _unused(llvm);

            auto [f, arg] = llvm.internal_function_definition(
                instr_name(instr),
                llvm.word_ty,
                {llvm.ptr_ty(context_ty),
                 llvm.int_ty(64),
                 llvm.ptr_ty(llvm.int_ty(64))});

            arg[0]->setName("ctx_ref");
            f->addParamAttr(0, Attribute::NoAlias);
            Value *block_base_gas_remaining = arg[1];
            block_base_gas_remaining->setName("block_base_gas_remaining");
            Value *ctx_gas_ref = arg[2];
            ctx_gas_ref->setName("ctx_gas_ref");

            auto *entry = llvm.basic_block("entry", f);
            llvm.insert_at(entry);
            auto *gas = llvm.load(llvm.int_ty(64), ctx_gas_ref);
            auto *r = llvm.add(gas, block_base_gas_remaining);
            llvm.ret(llvm.cast_word(r));
            return f;
        }

        Function *llvm_sar(Instruction const &instr)
        {
            SaveInsert const _unused(llvm);

            auto [f, args] = internal_op_definition(instr, 2);
            auto *entry = llvm.basic_block("entry", f);
            llvm.insert_at(entry);

            auto *a = args.var_args[0];
            auto *b = args.var_args[1];

            auto *isgt = llvm.ugt(a, llvm.lit_word(255));
            auto *then_lbl = llvm.basic_block("then_lbl", f);
            auto *else_lbl = llvm.basic_block("else_lbl", f);

            llvm.condbr(isgt, then_lbl, else_lbl, false);

            llvm.insert_at(then_lbl);
            llvm.ret(llvm.sar(b, llvm.lit_word(255)));

            llvm.insert_at(else_lbl);
            llvm.ret(llvm.sar(b, a));

            return f;
        }

        Function *llvm_signextend(Instruction const &instr)
        {
            SaveInsert const _unused(llvm);

            auto [f, args] = internal_op_definition(instr, 2);

            auto *a = args.var_args[0];
            auto *b = args.var_args[1];

            auto *entry = llvm.basic_block("entry", f);
            llvm.insert_at(entry);

            auto *isgt = llvm.ugt(a, llvm.lit_word(30));
            auto *then_lbl = llvm.basic_block("then_lbl", f);
            auto *else_lbl = llvm.basic_block("else_lbl", f);

            llvm.condbr(isgt, then_lbl, else_lbl, false);

            llvm.insert_at(then_lbl);
            llvm.ret(b);

            llvm.insert_at(else_lbl);

            auto *nbytes = llvm.sub(llvm.lit_word(31), a);
            auto *nbits = llvm.mul(nbytes, llvm.lit_word(8));
            llvm.ret(llvm.sar(llvm.shl(b, nbits), nbits));
            return f;
        }

        void emit_context_expand_memory(Value *ctx_ref, Value *min_size)
        {
            if (context_expand_memory_f == nullptr) {
                auto f = declare_symbol(
                    "context_expand_memory",
                    (void *)(context_expand_memory),
                    llvm.void_ty,
                    {
                        llvm.ptr_ty(context_ty),
                        llvm.int_ty(32),
                    });
                context_expand_memory_f = f;
            }
            llvm.call_void(context_expand_memory_f, {ctx_ref, min_size});
        };

        Value *
        llvm_memory_pre(int32_t width, Function *f, std::vector<Value *> &arg)
        {
            f->addParamAttr(0, Attribute::NoAlias);
            Value *ctx_ref = arg[0];
            ctx_ref->setName("ctx_ref");

            arg[1]->setName("gas");

            Value *offset;
            Value *mem_size_ptr;
            Value *mem_data_ptr_ptr;
            mem_size_ptr = arg[2];
            mem_size_ptr->setName("mem_size_ptr");

            mem_data_ptr_ptr = arg[3];
            mem_data_ptr_ptr->setName("mem_data_ptr_ptr");

            offset = arg[4];

            offset->setName("offset");
            auto *entry = llvm.basic_block("entry", f);
            auto *offset_err_lbl = llvm.basic_block("offset_err_lbl", f);
            auto *offset_ok_lbl = llvm.basic_block("offset_ok_lbl", f);
            auto *expand_mem_lbl = llvm.basic_block("expand_mem_lbl", f);
            auto *mem_ok_lbl = llvm.basic_block("mem_ok_lbl", f);

            llvm.insert_at(entry);

            uint256_t const max_offset =
                (uint64_t{1} << 29) - static_cast<uint32_t>(width);
            auto *isgt = llvm.ugt(offset, llvm.lit_word(max_offset));
            llvm.condbr(isgt, offset_err_lbl, offset_ok_lbl, false);

            llvm.insert_at(offset_err_lbl);
            exit_(ctx_ref, StatusCode::Error);

            llvm.insert_at(offset_ok_lbl);
            Value *offset_32 = llvm.cast_32(offset);

            Value *min_size = llvm.add(offset_32, llvm.i32(width));

            auto *mem_size = llvm.load(llvm.int_ty(32), mem_size_ptr);

            auto *is_out_of_bounds = llvm.ugt(min_size, mem_size);
            llvm.condbr(is_out_of_bounds, expand_mem_lbl, mem_ok_lbl, false);

            llvm.insert_at(expand_mem_lbl);
            emit_context_expand_memory(ctx_ref, min_size);
            update_memory_refs(ctx_ref, mem_size_ptr, mem_data_ptr_ptr);

            llvm.br(mem_ok_lbl);

            llvm.insert_at(mem_ok_lbl);

            Value *mem_data;
            mem_data = llvm.load(llvm.ptr_ty(llvm.int_ty(8)), mem_data_ptr_ptr);

            return llvm.gep(
                llvm.int_ty(8), mem_data, offset_32, "mem_data_offset");
        }

        Function *llvm_mload(Instruction const &instr)
        {
            SaveInsert const _unused(llvm);

            std::vector<Type *> arg_tys;

            arg_tys = {
                llvm.ptr_ty(context_ty),
                llvm.int_ty(64),
                llvm.ptr_ty(llvm.int_ty(32)), // memory size
                llvm.ptr_ty(llvm.ptr_ty(llvm.int_ty(8))), // memory data
                llvm.word_ty};
            auto [f, arg] = llvm.internal_function_definition(
                instr_name(instr), llvm.word_ty, arg_tys);

            Value *mem_data_offset = llvm_memory_pre(32, f, arg);

            Value *ret_val =
                llvm.bswap(llvm.load(llvm.word_ty, mem_data_offset));

            llvm.ret(ret_val);

            return f;
        }

        Function *llvm_mstore(Instruction const &instr)
        {
            SaveInsert const _unused(llvm);
            std::vector<Type *> arg_tys;

            arg_tys = {
                llvm.ptr_ty(context_ty),
                llvm.int_ty(64),
                llvm.ptr_ty(llvm.int_ty(32)), // memory size
                llvm.ptr_ty(llvm.ptr_ty(llvm.int_ty(8))), // memory data
                llvm.word_ty,
                llvm.word_ty};

            auto [f, arg] = llvm.internal_function_definition(
                instr_name(instr), llvm.void_ty, arg_tys);

            Value *mem_data_offset = llvm_memory_pre(32, f, arg);
            MONAD_VM_ASSERT(mem_data_offset);

            Value *value;
            value = arg[5];
            value->setName("value");

            llvm.store(llvm.bswap(value), mem_data_offset);
            llvm.ret_void();

            return f;
        }

        Function *llvm_mstore8(Instruction const &instr)
        {
            SaveInsert const _unused(llvm);

            std::vector<Type *> arg_tys;

            arg_tys = {
                llvm.ptr_ty(context_ty),
                llvm.int_ty(64),
                llvm.ptr_ty(llvm.int_ty(32)), // memory size
                llvm.ptr_ty(llvm.ptr_ty(llvm.int_ty(8))), // memory data
                llvm.word_ty,
                llvm.word_ty};

            auto [f, arg] = llvm.internal_function_definition(
                instr_name(instr), llvm.void_ty, arg_tys);

            Value *mem_data_offset = llvm_memory_pre(1, f, arg);

            Value *value;

            value = arg[5];

            value->setName("value");

            llvm.store(llvm.trunc_8(value), mem_data_offset);
            llvm.ret_void();

            return f;
        }

        Function *llvm_calldataload(Instruction const &instr)
        {
            SaveInsert const _unused(llvm);

            auto [f, arg] = llvm.internal_function_definition(
                instr_name(instr),
                llvm.word_ty,
                {llvm.ptr_ty(context_ty), llvm.int_ty(64), llvm.word_ty});

            f->addParamAttr(0, Attribute::NoAlias);
            Value *ctx_ref = arg[0];
            ctx_ref->setName("ctx_ref");

            arg[1]->setName("gas");

            Value *offset = arg[2];
            offset->setName("offset");

            auto *entry = llvm.basic_block("entry", f);
            auto *offset_err_lbl = llvm.basic_block("offset_err_lbl", f);
            auto *offset_lt_lbl = llvm.basic_block("offset_lt_lbl", f);
            auto *offset_partial_load_lbl =
                llvm.basic_block("offset_partial_load_lbl", f);
            auto *offset_full_load_lbl =
                llvm.basic_block("offset_full_load_lbl", f);

            llvm.insert_at(entry);

            Value *data_size_p = context_gep(
                ctx_ref,
                context_offset_env_input_data_size,
                "input_data_size_p");
            Value *data_size = llvm.load(llvm.int_ty(32), data_size_p);
            Value *data_size_256 = llvm.cast_word(data_size);
            Value *isge = llvm.uge(offset, data_size_256);
            llvm.condbr(isge, offset_err_lbl, offset_lt_lbl, false);

            llvm.insert_at(offset_err_lbl);
            llvm.ret(llvm.lit_word(0));

            llvm.insert_at(offset_lt_lbl);

            Value *offset_32 = llvm.cast_32(offset);
            Value *nbytes = llvm.sub(data_size, offset_32);
            Value *islt = llvm.ult(nbytes, llvm.i32(32));

            Value *data_p_p = context_gep(
                ctx_ref, context_offset_env_input_data, "input_data_p_p");
            Value *data_p = llvm.load(llvm.ptr_ty(llvm.int_ty(8)), data_p_p);
            Value *offset_data_p =
                llvm.gep(llvm.int_ty(8), data_p, {offset_32}, "offset_data_p");
            llvm.condbr(
                islt, offset_partial_load_lbl, offset_full_load_lbl, false);

            llvm.insert_at(offset_partial_load_lbl);
            Value *p = llvm.alloca_(llvm.word_ty, "p");
            llvm.store(llvm.lit_word(0), p);
            llvm.memcpy_(p, offset_data_p, nbytes);
            llvm.ret(llvm.bswap(llvm.load(llvm.word_ty, p)));

            llvm.insert_at(offset_full_load_lbl);
            llvm.ret(llvm.bswap(llvm.load(llvm.word_ty, offset_data_p)));

            return f;
        }

        Function *init_instr(Instruction const &instr)
        {
            OpCode const op = instr.opcode();
            switch (op) {
            case SStore:
                return ffi_runtime(instr, sstore<traits>);

            case Create:
                return ffi_runtime(instr, create<traits>);

            case Create2:
                return ffi_runtime(instr, create2<traits>);

            case DelegateCall:
                return ffi_runtime(instr, delegatecall<traits>);

            case StaticCall:
                return ffi_runtime(instr, staticcall<traits>);

            case Call:
                return ffi_runtime(instr, call<traits>);

            case CallCode:
                return ffi_runtime(instr, callcode<traits>);

            case SelfBalance:
                return ffi_runtime(instr, selfbalance);

            case Balance:
                return ffi_runtime(instr, balance<traits>);

            case ExtCodeHash:
                return ffi_runtime(instr, extcodehash<traits>);

            case ExtCodeSize:
                return ffi_runtime(instr, extcodesize<traits>);

            case SLoad:
                return ffi_runtime(instr, sload<traits>);

            case BlobHash:
                return ffi_runtime(instr, blobhash);

            case BlockHash:
                return ffi_runtime(instr, blockhash);

            case CallDataLoad:
                return llvm_calldataload(instr);

            case TLoad:
                return ffi_runtime(instr, tload);

            case Exp:
                return ffi_runtime(instr, exp<traits>);

            case Sha3:
                return ffi_runtime(instr, sha3);

            case MLoad:
                return llvm_mload(instr);

            case MStore:
                return llvm_mstore(instr);

            case MStore8:
                return llvm_mstore8(instr);

            case TStore:
                return ffi_runtime(instr, tstore);

            case CallDataCopy:
                return ffi_runtime(instr, calldatacopy);

            case CodeCopy:
                return ffi_runtime(instr, codecopy);

            case MCopy:
                return ffi_runtime(instr, mcopy);

            case ReturnDataCopy:
                return ffi_runtime(instr, returndatacopy);

            case ExtCodeCopy:
                return ffi_runtime(instr, extcodecopy<traits>);

            case Log:
                switch (instr.index()) {
                case 0:
                    return ffi_runtime(instr, log0);

                case 1:
                    return ffi_runtime(instr, log1);

                case 2:
                    return ffi_runtime(instr, log2);

                case 3:
                    return ffi_runtime(instr, log3);

                default:
                    MONAD_VM_ASSERT(instr.index() == 4);
                    return ffi_runtime(instr, log4);
                }

            case Address:
                return load_context_addr(instr, context_offset_env_recipient);

            case Coinbase:
                return load_evmc_tx_context_addr(
                    instr, offsetof(evmc_tx_context, block_coinbase));

            case Caller:
                return load_context_addr(instr, context_offset_env_sender);

            case Origin:
                return load_evmc_tx_context_addr(
                    instr, offsetof(evmc_tx_context, tx_origin));

            case GasLimit:
                return load_evmc_tx_context_uint64(
                    instr, offsetof(evmc_tx_context, block_gas_limit));

            case Number:
                return load_evmc_tx_context_uint64(
                    instr, offsetof(evmc_tx_context, block_number));

            case MSize:
                return load_context_uint32(instr, context_offset_memory_size);

            case CodeSize:
                return load_context_uint32(instr, context_offset_env_code_size);

            case CallDataSize:
                return load_context_uint32(
                    instr, context_offset_env_input_data_size);

            case Timestamp:
                return load_evmc_tx_context_uint64(
                    instr, offsetof(evmc_tx_context, block_timestamp));

            case ReturnDataSize:
                return load_context_uint64(
                    instr, context_offset_env_return_data_size);

            case ChainId:
                return load_evmc_tx_context_be(
                    instr, offsetof(evmc_tx_context, chain_id));

            case Difficulty:
                return load_evmc_tx_context_be(
                    instr, offsetof(evmc_tx_context, block_prev_randao));

            case BlobBaseFee:
                return load_evmc_tx_context_be(
                    instr, offsetof(evmc_tx_context, blob_base_fee));

            case BaseFee:
                return load_evmc_tx_context_be(
                    instr, offsetof(evmc_tx_context, block_base_fee));

            case GasPrice:
                return load_evmc_tx_context_be(
                    instr, offsetof(evmc_tx_context, tx_gas_price));

            case CallValue:
                return load_context_be(instr, context_offset_env_value);

            case Gas:
                return llvm_gas(instr);

            case Byte:
                return llvm_byte(instr);

            case SignExtend:
                return llvm_signextend(instr);

            case SDiv:
                return llvm_sdivop(instr);

            case Div:
                return llvm_divop(instr, &LLVMState::udiv);

            case Mod:
                return llvm_divop(instr, &LLVMState::urem);

            case SMod:
                return llvm_divop(instr, &LLVMState::srem);

            case Shl:
                return llvm_shiftop(instr, &LLVMState::shl);

            case Shr:
                return llvm_shiftop(instr, &LLVMState::shr);

            case Sar:
                return llvm_sar(instr);

            case IsZero:
                return llvm_unop(instr, &LLVMState::is_zero);

            case AddMod:
                return llvm_modop(instr, &LLVMState::addmod);

            case MulMod:
                return llvm_modop(instr, &LLVMState::mulmod);

            case Lt:
                return llvm_binop(instr, &LLVMState::ult);

            case Gt:
                return llvm_binop(instr, &LLVMState::ugt);

            case SLt:
                return llvm_binop(instr, &LLVMState::slt);

            case SGt:
                return llvm_binop(instr, &LLVMState::sgt);

            case Eq:
                return llvm_binop(instr, &LLVMState::equ);

            case XOr:
                return llvm_binop(instr, &LLVMState::xor_);

            case Or:
                return llvm_binop(instr, &LLVMState::or_);

            case And:
                return llvm_binop(instr, &LLVMState::and_);

            case Not:
                return llvm_unop(instr, &LLVMState::not_);

            case Sub:
                return llvm_binop(instr, &LLVMState::sub);

            case Mul:
                return llvm_binop(instr, &LLVMState::mul);

            case Clz:
                return llvm_unop(instr, &LLVMState::clz);

            default:
                MONAD_VM_ASSERT(op == Add);
                return llvm_binop(instr, &LLVMState::add);
            }
        };
    };
};
