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

#include <category/vm/llvm/dependency_blocks.hpp>
#include <category/vm/llvm/llvm_state.hpp>

#include <category/vm/evm/traits.hpp>
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

        void init_jumptable()
        {
            jumptable_max_offset = 0;
            jumptable_min_offset = std::numeric_limits<byte_offset>::max();

            for (auto const &[k, _] : jumpdest_tbl) {
                jumptable_min_offset = std::min(jumptable_min_offset, k);
                jumptable_max_offset = std::max(jumptable_max_offset, k);
            }

            jumptable_err_offset = jumptable_max_offset + 1;

            byte_offset sz = jumptable_err_offset - jumptable_min_offset + 1;

            jumptable_ty = llvm.array_ty(block_addr_ty, sz);

            std::vector<Constant *> vals(sz);

            for (byte_offset i = 0; i < sz; ++i) {
                vals[i] = llvm.block_address(lookup_jumpdest(
                    static_cast<uint256_t>(i + jumptable_min_offset)));
            }

            jumptable = llvm.const_array(vals, "jumptable");
        }

        BasicBlock *lookup_jumpdest(uint256_t c)
        {
            if (c > std::numeric_limits<byte_offset>::max()) {
                return error_lbl();
            }

            auto item = jumpdest_tbl.find(static_cast<byte_offset>(c));
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
                                [&](InstrIdx const &) {
                                    return indirectbr_lbl(i);
                                },
                            },
                            else_v);

                        llvm.condbr(isz, then_lbl, else_lbl);
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
                llvm.debug("stop\n");
                llvm.br(return_lbl());
                return;
            case Return:
                llvm.debug("return\n");
                prep_for_return(args[0], args[1]);
                llvm.br(return_lbl());
                return;
            case Revert:
                llvm.debug("revert\n");
                prep_for_return(args[0], args[1]);
                llvm.br(revert_lbl());
                return;
            case SelfDestruct:
                llvm.debug("self destruct\n");
                selfdestruct_(args[0]);
                return;
            default:
                std::cerr << std::format("{}\n", term);
                llvm.debug("invalid instruction\n");
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
                llvm.ptr_ty(llvm.word_ty),
                stack_top,
                {llvm.i32(i)},
                "stacktop_offset");
        }

        void update_gas(int64_t const block_base_gas)
        {

            if (update_gas_f == nullptr) {
                SaveInsert const _unused(llvm);
                auto [f, arg] = llvm.internal_function_definition(
                    "update_gas",
                    llvm.void_ty,
                    {llvm.ptr_ty(context_ty),
                     llvm.ptr_ty(llvm.int_ty(64)),
                     llvm.int_ty(64)});
                update_gas_f = f;
                auto *entry = llvm.basic_block("entry", f);
                llvm.insert_at(entry);

                Value *ctx_ref = arg[0];
                ctx_ref->setName("ctx_ref");
                Value *gas_ref = arg[1];
                gas_ref->setName("gas_ref");
                Value *block_base_gas = arg[2];
                block_base_gas->setName("block_base_gas");

                auto *gas = llvm.load(llvm.int_ty(64), gas_ref);
                auto *gas1 = llvm.sub(gas, block_base_gas);
                llvm.store(gas1, gas_ref);
                auto *gas_lt_zero = llvm.slt(gas1, llvm.lit(64, 0));

                auto *gas_ok_lbl = llvm.basic_block("gas_ok_lbl", f);
                auto *gas_err_lbl = llvm.basic_block("gas_err_lbl", f);

                llvm.condbr(gas_lt_zero, gas_err_lbl, gas_ok_lbl);

                llvm.insert_at(gas_err_lbl);

                llvm.call_void(
                    exit_f,
                    {ctx_ref,
                     llvm.lit(64, static_cast<uint64_t>(StatusCode::Error))});
                llvm.unreachable();

                llvm.insert_at(gas_ok_lbl);
                llvm.ret_void();
            }

            llvm.call_void(
                update_gas_f,
                {g_ctx_ref,
                 g_ctx_gas_ref,
                 llvm.lit(64, static_cast<uint64_t>(block_base_gas))});
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

                update_gas(blk.block_base_gas);

                Value *stack_top = load_stack_top_p();

                // std::cerr << std::format("block {}", blk);

                for (auto const &[i, instr] : blk.instrs) {
                    // std::cerr << std::format("i {}", i);
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

        Value *evm_stack_begin = nullptr;
        Value *evm_stack_end = nullptr;
        Value *evm_stack_top_p = nullptr;

        Value *jumptable = nullptr;
        byte_offset jumptable_min_offset;
        byte_offset jumptable_max_offset;
        byte_offset jumptable_err_offset;
        Type *block_addr_ty = llvm.ptr_ty(llvm.int_ty(8));
        Type *jumptable_ty;

        std::unordered_map<std::string, Function *> llvm_opcode_tbl;
        // ^ string instead of opcode for Log

        std::unordered_map<byte_offset, BasicBlock *> block_tbl;
        std::unordered_map<byte_offset, BasicBlock *> jumpdest_tbl;

        Type *context_ty = llvm.void_ty;

        Function *exit_f = init_exit();
        Function *selfdestruct_f = nullptr;
        Function *update_gas_f = nullptr;

        Value *jump_mem = nullptr;
        BasicBlock *jump_lbl = nullptr;
        BasicBlock *error_lbl_v = nullptr;
        BasicBlock *return_lbl_v = nullptr;
        BasicBlock *revert_lbl_v = nullptr;

        BasicBlock *indirectbr_lbl_v = nullptr;
        PHINode *indirectbr_phi = nullptr;
        IndirectBrInst *indirectbr_v = nullptr;

        std::vector<Value *> value_tbl;

        BasicBlock *entry = nullptr;
        Function *contract = nullptr;

        Function *evm_push_f = nullptr;
        Function *evm_pop_f = nullptr;

        void copy_gas(Value *from, Value *to)
        {
            auto *gas = llvm.load(llvm.int_ty(64), from);
            llvm.store(gas, to);
        }

        void store_stack_top_p(Value *stack_top)
        {
            llvm.debug("storing new stack_top_p\n");
            llvm.store(stack_top, evm_stack_top_p);
        }

        Value *load_stack_top_p()
        {
            llvm.debug("loading stacktop_p\n");
            return llvm.load(llvm.ptr_ty(llvm.word_ty), evm_stack_top_p);
        }

        BasicBlock *error_lbl()
        {
            if (error_lbl_v == nullptr) {
                SaveInsert const _unused(llvm);
                error_lbl_v = llvm.basic_block("error_lbl", contract);
                llvm.insert_at(error_lbl_v);
                exit_(StatusCode::Error);
            }
            return error_lbl_v;
        }

        BasicBlock *return_lbl()
        {
            if (return_lbl_v == nullptr) {
                SaveInsert const _unused(llvm);
                return_lbl_v = llvm.basic_block("return_lbl", contract);
                llvm.insert_at(return_lbl_v);
                exit_(StatusCode::Success);
            }
            return return_lbl_v;
        }

        BasicBlock *revert_lbl()
        {
            if (revert_lbl_v == nullptr) {
                SaveInsert const _unused(llvm);
                revert_lbl_v = llvm.basic_block("revert_lbl", contract);
                llvm.insert_at(revert_lbl_v);
                exit_(StatusCode::Revert);
            }
            return revert_lbl_v;
        }

        // void init_indirectbr_block()
        // {
        //     if (indirectbr_lbl_v == nullptr) {
        //         return;
        //     }
        //     init_jumptable();
        //     SaveInsert const _unused(llvm);
        //     llvm.insert_at(indirectbr_lbl_v);
        //     Value *indirectbr_phi = llvm.phi(llvm.word_ty, indirectbr_phis);
        //
        //     Value *is_lte_max_offset = llvm.ule(
        //         indirectbr_phi,
        //         llvm.lit_word(static_cast<uint256_t>(jumptable_max_offset)));
        //
        //     Value *lte_offset = llvm.select(
        //         is_lte_max_offset,
        //         llvm.cast_64(indirectbr_phi),
        //         llvm.u64(jumptable_err_offset + jumptable_min_offset));
        //
        //     Value *is_gte_min_offset =
        //         llvm.uge(lte_offset, llvm.u64(jumptable_min_offset));
        //
        //     Value *gte_offset = llvm.select(
        //         is_gte_min_offset,
        //         lte_offset,
        //         llvm.u64(jumptable_err_offset + jumptable_min_offset));
        //
        //     Value *sub_offset = // BAL: eliminate this sub by rewriting the
        //                         // jumptable address
        //         llvm.sub(gte_offset, llvm.u64(jumptable_min_offset));
        //
        //     Value *p = llvm.gep(
        //         jumptable_ty,
        //         jumptable,
        //         {llvm.u32(0), sub_offset},
        //         "jumpdest_p");
        //
        //     Value *jd_addr = llvm.load(llvm.ptr_ty(block_addr_ty), p);
        //
        //     std::vector<BasicBlock *> lbls;
        //
        //     for (auto const &[_, lbl] : jumpdest_tbl) {
        //         lbls.push_back(lbl);
        //     }
        //     lbls.push_back(error_lbl());
        //
        //     llvm.indirectbr(jd_addr, lbls);
        // }
        //
        BasicBlock *indirectbr_lbl(InstrIdx i)
        {
            if (jumpdest_tbl.size() == 0) {
                return error_lbl();
            }

            if (indirectbr_lbl_v == nullptr) {
                init_jumptable();
                indirectbr_lbl_v = llvm.basic_block("indirectbr_lbl", contract);
                SaveInsert const _unused(llvm);
                llvm.insert_at(indirectbr_lbl_v);

                indirectbr_phi = llvm.phi(llvm.word_ty);

                Value *is_lte_max_offset = llvm.ule(
                    indirectbr_phi,
                    llvm.lit_word(
                        static_cast<uint256_t>(jumptable_max_offset)));

                Value *lte_offset = llvm.select(
                    is_lte_max_offset,
                    llvm.cast_64(indirectbr_phi),
                    llvm.u64(jumptable_err_offset + jumptable_min_offset));

                Value *is_gte_min_offset =
                    llvm.uge(lte_offset, llvm.u64(jumptable_min_offset));

                Value *gte_offset = llvm.select(
                    is_gte_min_offset,
                    lte_offset,
                    llvm.u64(jumptable_err_offset + jumptable_min_offset));

                Value *sub_offset = // BAL: eliminate this sub by rewriting the
                                    // jumptable address
                    llvm.sub(gte_offset, llvm.u64(jumptable_min_offset));

                Value *p = llvm.gep(
                    jumptable_ty,
                    jumptable,
                    {llvm.u32(0), sub_offset},
                    "jumpdest_p");

                Value *jd_addr = llvm.load(llvm.ptr_ty(block_addr_ty), p);
                indirectbr_v = llvm.indirectbr(jd_addr);

                llvm.indirect_br_add_dest(indirectbr_v, error_lbl());
                for (auto const &[_, lbl] : jumpdest_tbl) {
                    llvm.indirect_br_add_dest(indirectbr_v, lbl);
                }
            }

            llvm.phi_add_incoming(
                indirectbr_phi, value_tbl[i], llvm.get_insert());

            return indirectbr_lbl_v;
        }

        void contract_start()
        {
            auto [contractf, arg] = llvm.external_function_definition(
                "contract",
                llvm.void_ty,
                {llvm.ptr_ty(llvm.word_ty), llvm.ptr_ty(context_ty)});
            contractf->addFnAttr(Attribute::NoReturn);
            contract = contractf;

            entry = llvm.basic_block("entry", contract);

            llvm.insert_at(entry);

            // BAL: should the stack be allocated here instead of passed in?
            evm_stack_begin = arg[0];
            evm_stack_begin->setName("evm_stack_begin");
            g_ctx_ref = arg[1];
            g_ctx_ref->setName("ctx_ref");

            // llvm.comment("init.the.gas");
            g_ctx_gas_ref = context_gep(
                g_ctx_ref, context_offset_gas_remaining, "ctx_gas_ref");

            // llvm.comment("init.the.stack");

            evm_stack_end = llvm.gep(
                llvm.word_ty,
                evm_stack_begin,
                {llvm.u64(1024)},
                "evm_stack_end");

            evm_stack_top_p =
                llvm.alloca_(llvm.ptr_ty(llvm.word_ty), "evm_stack_top_p");

            store_stack_top_p(evm_stack_begin);

            llvm.insert_at(entry);
        }

        Value *evm_stack_idx(Value *stack_top, int64_t i)
        {
            return llvm.gep(
                llvm.word_ty, stack_top, {llvm.i64(i)}, "evm_stack_idx");
        };

        void contract_finish()
        {
            llvm.insert_at(entry);
            MONAD_VM_ASSERT(dep_ir.blocks.size() > 0);
            llvm.br(get_block_lbl(dep_ir.blocks.front().offset));
        };

        bool reads_ctx_gas(OpCode op)
        {
            return (
                op == Balance || op == BlobHash || op == BlockHash ||
                op == Call || op == CallCode || op == CallDataCopy ||
                op == CallDataLoad || op == CodeCopy || op == Create ||
                op == Create2 || op == DelegateCall || op == Exp ||
                op == ExtCodeCopy || op == ExtCodeHash || op == ExtCodeSize ||
                op == Log || op == MCopy || op == MLoad || op == MStore ||
                op == MStore8 || op == ReturnDataCopy || op == SLoad ||
                op == SStore || op == SelfBalance || op == Sha3 ||
                op == StaticCall || op == TLoad || op == TStore);
        };

        bool writes_ctx_gas(OpCode op)
        {
            return (
                op == Balance || op == Call || op == CallCode ||
                op == CallDataCopy || op == CodeCopy || op == Create ||
                op == Create2 || op == DelegateCall || op == Exp ||
                op == ExtCodeCopy || op == ExtCodeHash || op == ExtCodeSize ||
                op == Log || op == MCopy || op == MLoad || op == MStore ||
                op == MStore8 || op == ReturnDataCopy || op == SLoad ||
                op == SStore || op == Sha3 || op == StaticCall);
        };

        std::string to_register_name(byte_offset blkId, InstrIdx i)
        {
            return std::format("v{}_{}", blkId, i);
        }

        void
        emit_instr(byte_offset blkId, InstrIdx i, struct EvmInstr const &ei)
        {
            Function *f;
            auto nm = instr_name(ei.instr);

            auto item = llvm_opcode_tbl.find(nm);
            if (item != llvm_opcode_tbl.end()) {
                f = item->second;
            }
            else {
                f = init_instr(ei.instr);
                llvm_opcode_tbl.insert({nm, f});
            }

            std::vector<Value *> args;

            args.push_back(g_ctx_ref);

            auto *g = llvm.lit(64, ei.remaining_block_base_gas);
            args.push_back(g);

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
        };

        std::tuple<Value *, BasicBlock *> get_jump_info()
        {
            if (jump_mem == nullptr) {
                SaveInsert const _unused(llvm);

                MONAD_VM_ASSERT(jump_lbl == nullptr);

                llvm.insert_at(entry);
                jump_mem = llvm.alloca_(llvm.word_ty, "jump_mem");

                jump_lbl = llvm.basic_block("do_jump", contract);
            }

            return std::tuple(jump_mem, jump_lbl);
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

        void exit_(StatusCode status)
        {
            llvm.call_void(
                exit_f,
                {g_ctx_ref, llvm.lit(64, static_cast<uint64_t>(status))});
            llvm.unreachable();
        }

        void check_underflow(int64_t low, Value *stack_top, byte_offset offset)
        {
            if (low >= 0) {
                llvm.debug("no need to check underflow\n");
                return;
            }
            auto *no_underflow_lbl = llvm.basic_block(
                std::format("no_underflow_lbl_{}", offset), contract);

            auto *stack_low = evm_stack_idx(stack_top, low);

            auto *low_pred = llvm.slt(stack_low, evm_stack_begin);
            llvm.condbr(low_pred, error_lbl(), no_underflow_lbl);

            llvm.insert_at(no_underflow_lbl);
        };

        void check_overflow(int64_t high, Value *stack_top, byte_offset offset)
        {
            if (high <= 0) {
                llvm.debug("no need to check overflow\n");
                return;
            }
            auto *no_overflow_lbl = llvm.basic_block(
                std::format("no_overflow_lbl_{}", offset), contract);

            auto *stack_high = evm_stack_idx(stack_top, high);

            auto *high_pred = llvm.sgt(stack_high, evm_stack_end);
            llvm.condbr(high_pred, error_lbl(), no_overflow_lbl);

            llvm.insert_at(no_overflow_lbl);
        };

        BasicBlock *get_block_lbl(byte_offset offset)
        {
            auto item = block_tbl.find(offset);
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
            return llvm.gep(
                llvm.int_ty(8), ctx_ref, {llvm.lit(64, offset)}, nm);
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
            auto *b = arg[1];
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

        Function *load_context_be(Instruction const &instr, uint64_t offset)
        {
            SaveInsert const _unused(llvm);

            auto [f, vctx] = context_fun(instr);
            auto *ref = context_gep(vctx, offset, "context_be");
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
            auto *b = args.var_args[1];
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
            llvm.condbr(llvm.eq(n, llvm.lit_word(0)), denom_is_0, denom_not_0);

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
            llvm.condbr(llvm.eq(denom, zero), ret_zero, try_denominator_neg1);

            llvm.insert_at(try_denominator_neg1); // check for denominator is -1
            llvm.condbr(llvm.eq(denom, neg1), try_overflow_semantics, ret_sdiv);

            llvm.insert_at(
                try_overflow_semantics); // check for numerator is minbound
            llvm.condbr(llvm.eq(numer, minbound), ret_overflow, ret_sdiv);

            return f;
        }

        Function *llvm_divop(
            Instruction const &instr,
            Value *(LLVMState::*method)(Value *, Value *))
        {
            SaveInsert const _unused(llvm);

            auto [f, args] = internal_op_definition(instr, 2);
            Value *numer = args.var_args[0];
            Value *denom = args.var_args[1];
            auto *entry = llvm.basic_block("entry", f);
            llvm.insert_at(entry);

            auto *isz = llvm.eq(denom, llvm.lit_word(0));
            auto *then_lbl = llvm.basic_block("then_lbl", f);
            auto *else_lbl = llvm.basic_block("else_lbl", f);

            llvm.condbr(isz, then_lbl, else_lbl);

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
            auto *b = args.var_args[1];

            auto *isgt = llvm.ugt(a, llvm.lit_word(255));
            auto *then_lbl = llvm.basic_block("then_lbl", f);
            auto *else_lbl = llvm.basic_block("else_lbl", f);

            llvm.condbr(isgt, then_lbl, else_lbl);

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

            llvm.condbr(isgt, then_lbl, else_lbl);

            llvm.insert_at(then_lbl);
            llvm.ret(llvm.lit_word(0));

            llvm.insert_at(else_lbl);

            auto *nbytes = llvm.sub(llvm.lit_word(31), a);
            auto *nbits = llvm.mul(nbytes, llvm.lit_word(8));
            llvm.ret(llvm.and_(llvm.shr(b, nbits), llvm.lit_word(255)));
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

            llvm.condbr(isgt, then_lbl, else_lbl);

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

            llvm.condbr(isgt, then_lbl, else_lbl);

            llvm.insert_at(then_lbl);
            llvm.ret(b);

            llvm.insert_at(else_lbl);

            auto *nbytes = llvm.sub(llvm.lit_word(31), a);
            auto *nbits = llvm.mul(nbytes, llvm.lit_word(8));
            llvm.ret(llvm.sar(llvm.shl(b, nbits), nbits));
            return f;
        }

        Function *init_instr(Instruction const &instr)
        {
            auto op = instr.opcode();
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
                return ffi_runtime(instr, calldataload);

            case MLoad:
                return ffi_runtime(instr, mload);

            case TLoad:
                return ffi_runtime(instr, tload);

            case Exp:
                return ffi_runtime(instr, exp<traits>);

            case Sha3:
                return ffi_runtime(instr, sha3);

            case MStore:
                return ffi_runtime(instr, mstore);

            case MStore8:
                return ffi_runtime(instr, mstore8);

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
                return load_context_addr(
                    instr, context_offset_env_tx_context_block_coinbase);

            case Caller:
                return load_context_addr(instr, context_offset_env_sender);

            case Origin:
                return load_context_addr(
                    instr, context_offset_env_tx_context_origin);

            case GasLimit:
                return load_context_uint64(
                    instr, context_offset_env_tx_context_block_gas_limit);

            case Number:
                return load_context_uint64(
                    instr, context_offset_env_tx_context_block_number);

            case MSize:
                return load_context_uint32(instr, context_offset_memory_size);

            case CodeSize:
                return load_context_uint32(instr, context_offset_env_code_size);

            case CallDataSize:
                return load_context_uint32(
                    instr, context_offset_env_input_data_size);

            case Timestamp:
                return load_context_uint64(
                    instr, context_offset_env_tx_context_block_timestamp);

            case ReturnDataSize:
                return load_context_uint64(
                    instr, context_offset_env_return_data_size);

            case ChainId:
                return load_context_be(
                    instr, context_offset_env_tx_context_chain_id);

            case Difficulty:
                return load_context_be(
                    instr, context_offset_env_tx_context_block_prev_randao);

            case BlobBaseFee:
                return load_context_be(
                    instr, context_offset_env_tx_context_blob_base_fee);

            case BaseFee:
                return load_context_be(
                    instr, context_offset_env_tx_context_block_base_fee);

            case GasPrice:
                return load_context_be(
                    instr, context_offset_env_tx_context_tx_gas_price);

            case CallValue:
                return load_context_be(instr, context_offset_env_value);

            case Gas:
                return nullptr; // Gas opcode is inlined

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

            default:
                MONAD_VM_ASSERT(op == Add);
                return llvm_binop(instr, &LLVMState::add);
            }
        };
    };
};
