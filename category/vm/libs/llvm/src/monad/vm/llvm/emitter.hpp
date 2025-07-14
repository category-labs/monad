#pragma once

#include <monad/vm/llvm/llvm_state.hpp>
#include <monad/vm/llvm/virtual_stack.hpp>

#include <monad/vm/runtime/call.hpp>
#include <monad/vm/runtime/create.hpp>
#include <monad/vm/runtime/data.hpp>
#include <monad/vm/runtime/environment.hpp>
#include <monad/vm/runtime/keccak.hpp>
#include <monad/vm/runtime/log.hpp>
#include <monad/vm/runtime/math.hpp>
#include <monad/vm/runtime/memory.hpp>
#include <monad/vm/runtime/selfdestruct.hpp>
#include <monad/vm/runtime/storage.hpp>

namespace monad::vm::llvm
{
    using namespace monad::vm::compiler;
    using namespace monad::vm::runtime;

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

    inline bool has_ctx_param(Instruction const &instr)
    {
        auto oc = instr.opcode();
        return (
            oc == Gas || oc == Number || oc == MSize || oc == CodeSize ||
            oc == Timestamp || oc == ReturnDataSize || oc == ChainId ||
            oc == Difficulty || oc == BlobBaseFee || oc == BaseFee ||
            oc == GasPrice || oc == Coinbase || oc == Address || oc == Caller ||
            oc == Origin || oc == GasLimit || oc == SStore || oc == BlobHash ||
            oc == BlockHash || oc == TLoad || oc == MLoad ||
            oc == CallDataLoad || oc == SelfBalance || oc == ExtCodeHash ||
            oc == ExtCodeSize || oc == SLoad || oc == Balance || oc == Sha3 ||
            oc == Exp || oc == Log || oc == MStore || oc == MStore8 ||
            oc == TStore || oc == CallDataCopy || oc == CodeCopy ||
            oc == MCopy || oc == ReturnDataCopy || oc == Create ||
            oc == Create2 || oc == ExtCodeCopy || oc == DelegateCall ||
            oc == StaticCall || oc == Call || oc == CallCode ||
            oc == CallValue || oc == CallDataSize);
    }

    inline bool has_gas_param(Instruction const &instr)
    {
        auto oc = instr.opcode();
        return (
            oc == Gas || oc == SStore || oc == Create || oc == Create2 ||
            oc == DelegateCall || oc == StaticCall || oc == Call ||
            oc == CallCode);
    }

    struct Emitter
    {

    public:
        Emitter(LLVMState &llvm, BasicBlocksIR const &ir)
            : llvm(llvm)
            , ir(ir)
        {
        }

        template <evmc_revision Rev>
        void emit_contract()
        {
            contract_start();

            for (auto const &blk : ir.blocks()) {

                base_gas_remaining = block_base_gas<Rev>(blk);

                bool const skip_block = block_begin<Rev>(blk);

                if (skip_block) {
                    continue;
                }

                for (auto const &instr : blk.instrs) {
                    base_gas_remaining -= instr.static_gas_cost();

                    emit_instr<Rev>(instr);
                }

                base_gas_remaining -=
                    terminator_static_gas<Rev>(blk.terminator);

                terminate_block<Rev>(blk);
            }

            contract_finish();
        }

    private:
        LLVMState &llvm;
        BasicBlocksIR const &ir;

        VirtualStack virtual_stack;

        Value *ctx_ref = nullptr;
        Value *evm_stack = nullptr;
        Value *evm_stack_height = nullptr;

        std::unordered_map<std::string, Function *> llvm_opcode_tbl;
        // ^ string instead of opcode for Log

        std::vector<std::tuple<byte_offset, BasicBlock *>> jumpdests;

        Type *context_ty = llvm.void_ty;

        Function *exit_f = init_exit();
        Function *block_begin_f = init_block_begin();

        std::unordered_map<byte_offset, BasicBlock *> block_tbl;

        Value *jump_mem = nullptr;
        BasicBlock *jump_lbl = nullptr;
        BasicBlock *entry = nullptr;
        Function *contract = nullptr;

        Function *stop_f = nullptr;
        Function *return_f = nullptr;
        Function *selfdestruct_f = nullptr;
        Function *revert_f = nullptr;
        int64_t base_gas_remaining;
        Function *evm_push_f = nullptr;
        Function *evm_pop_f = nullptr;

        void contract_start()
        {
            auto [contractf, arg] = llvm.external_function_definition(
                "contract",
                llvm.void_ty,
                {llvm.ptr_ty(llvm.word_ty), llvm.ptr_ty(context_ty)});
            contractf->addFnAttr(Attribute::NoReturn);
            contract = contractf;

            evm_stack = arg[0];
            ctx_ref = arg[1];

            entry = llvm.basic_block("entry", contract);
            llvm.insert_at(entry);

            evm_stack_height = llvm.alloca_(llvm.int_ty(32));
            llvm.store(llvm.lit(32, 0), evm_stack_height);

            set_stack_vars(evm_stack, evm_stack_height);
        }

        void emit_jumptable()
        {
            MONAD_VM_ASSERT(jump_lbl != nullptr);
            MONAD_VM_ASSERT(jump_mem != nullptr);
            MONAD_VM_ASSERT(jumpdests.size() > 0);

            auto *err_ret = llvm.basic_block("invalid_jump_dest", contract);

            llvm.insert_at(err_ret);
            exit_(ctx_ref, StatusCode::Error);

            llvm.insert_at(jump_lbl);
            auto *d = llvm.load(llvm.word_ty, jump_mem);

            // create switch
            auto *jump_lbl_switch = llvm.switch_(
                d, err_ret, static_cast<unsigned>(jumpdests.size()));

            for (auto [k, v] : jumpdests) {
                auto *c = llvm.lit_word(static_cast<uint256_t>(k));
                jump_lbl_switch->addCase(c, v);
            }
        };

        void set_stack_vars(Value *evm_stackv, Value *evm_stack_heightv)
        {
            evm_stack = evm_stackv;
            evm_stack_height = evm_stack_heightv;
        };

        // spill virtual stack values to the evm runtime stack
        void stack_spill()
        {
            for (auto *v : virtual_stack.virt_stack) {
                evm_push(v);
            }
        };

        // unspill values from the evm runtime stack to the virtual stack (if
        // necessary)
        void stack_unspill(int64_t low)
        {
            for (; low < 0; ++low) {
                Value *v = evm_pop();
                virtual_stack.virt_stack.insert(
                    virtual_stack.virt_stack.begin(), v);
            }
        };

        void evm_push(Value *v)
        {
            if (evm_push_f == nullptr) {
                evm_push_f = init_evm_push();
            }
            llvm.call_void(evm_push_f, {v, evm_stack, evm_stack_height});
        };

        Value *evm_pop()
        {
            if (evm_pop_f == nullptr) {
                evm_pop_f = init_evm_pop();
            }
            return llvm.call(evm_pop_f, {evm_stack, evm_stack_height});
        };

        Function *init_evm_push()
        {
            llvm.save_insert();

            auto [fun, arg] = llvm.internal_function_definition(
                "evm_push",
                llvm.void_ty,
                {llvm.word_ty,
                 llvm.ptr_ty(llvm.word_ty),
                 llvm.ptr_ty(llvm.int_ty(32))});

            Value *val = arg[0];
            Value *evm_stackp = arg[1];
            Value *heightp = arg[2];

            auto *entry = llvm.basic_block("entry", fun);
            llvm.insert_at(entry);

            auto *height = llvm.load(llvm.int_ty(32), heightp);
            auto *top = get_evm_stack_top(evm_stackp, height);
            llvm.store(val, top);
            auto *height1 = llvm.add(llvm.lit(32, 1), height);
            llvm.store(height1, heightp);
            llvm.ret_void();
            llvm.restore_insert();
            return fun;
        };

        Value *get_evm_stack_top(Value *evm_stackp, Value *height)
        {
            return llvm.gep(llvm.word_ty, evm_stackp, {height});
        };

        Function *init_evm_pop()
        {
            llvm.save_insert();
            auto [fun, arg] = llvm.internal_function_definition(
                "evm_pop",
                llvm.word_ty,
                {llvm.ptr_ty(llvm.word_ty), llvm.ptr_ty(llvm.int_ty(32))});

            Value *evm_stackp = arg[0];
            Value *heightp = arg[1];

            auto *entry = llvm.basic_block("entry", fun);

            llvm.insert_at(entry);

            auto *height = llvm.load(llvm.int_ty(32), heightp);
            auto *height1 = llvm.sub(height, llvm.lit(32, 1));
            llvm.store(height1, heightp);

            auto *top = get_evm_stack_top(evm_stackp, height1);
            auto *val = llvm.load(llvm.word_ty, top);

            llvm.ret(val);
            llvm.restore_insert();
            return fun;
        };

        void contract_finish()
        {
            llvm.insert_at(entry);
            MONAD_VM_ASSERT(ir.blocks().size() > 0);
            llvm.br(get_block_lbl(ir.blocks().front()));

            // add jump table if needed
            if (jump_lbl != nullptr) {
                emit_jumptable();
            }
        }

        template <evmc_revision Rev>
        void emit_instr(Instruction const &instr)
        {
            auto op = instr.opcode();

            switch (op) {
            case Push:
                virtual_stack.push(llvm.lit_word(instr.immediate_value()));
                break;

            case Pc:
                virtual_stack.push(llvm.lit_word(instr.pc()));
                break;

            case Dup:
                virtual_stack.dup(instr.index());
                break;

            case Swap:
                virtual_stack.swap(instr.index());
                break;

            case Pop:
                virtual_stack.pop();
                break;

            default:
                Function *f;
                auto nm = instr_name(instr);

                auto item = llvm_opcode_tbl.find(nm);
                if (item != llvm_opcode_tbl.end()) {
                    f = item->second;
                }
                else {
                    f = init_instr<Rev>(instr);
                    llvm_opcode_tbl.insert({nm, f});
                }

                std::vector<Value *> args;

                if (has_ctx_param(instr)) {
                    args.push_back(ctx_ref);
                }

                for (auto i = 0; i < instr.stack_args(); ++i) {
                    auto *v = virtual_stack.pop();
                    args.push_back(v);
                }

                if (has_gas_param(instr)) {
                    auto *g =
                        llvm.lit(64, static_cast<uint64_t>(base_gas_remaining));
                    args.push_back(g);
                }

                if (instr.increases_stack()) {
                    virtual_stack.push(llvm.call(f, args));
                }
                else {
                    llvm.call_void(f, args);
                }
            }
        };

        std::tuple<Value *, BasicBlock *> get_jump_info()
        {
            if (jump_mem == nullptr) {
                MONAD_VM_ASSERT(jump_lbl == nullptr);

                llvm.save_insert();
                llvm.insert_at(entry);
                jump_mem = llvm.alloca_(llvm.word_ty);
                llvm.restore_insert();

                jump_lbl = llvm.basic_block("do_jump", contract);
            }

            return std::tuple(jump_mem, jump_lbl);
        };

        void emit_jump(Value *v)
        {
            if (ir.jump_dests().size() == 0) {
                exit_(ctx_ref, StatusCode::Error);
            }
            else {
                auto [p, lbl] = get_jump_info();
                llvm.store(v, p);
                llvm.br(lbl);
            }
        };

        bool is_jumpdest(Block const &blk)
        {
            auto item = ir.jump_dests().find(blk.offset);
            return (item != ir.jump_dests().end());
        };

        Block const &get_fallthrough_block(Block const &blk)
        {
            auto dest = blk.fallthrough_dest;
            MONAD_VM_ASSERT(
                dest != INVALID_BLOCK_ID && dest < ir.blocks().size());
            return ir.blocks()[dest];
        };

        void fallthrough(Block const &blk)
        {
            auto next_blk = get_fallthrough_block(blk);
            MONAD_VM_ASSERT(is_jumpdest(next_blk));
            stack_spill();
            llvm.br(get_block_lbl(next_blk));
        };

        void jump()
        {
            auto *v = virtual_stack.pop();
            stack_spill();
            emit_jump(v);
        };

        void jumpi(Block const &blk)
        {
            auto *v = virtual_stack.pop();
            auto *b = virtual_stack.pop();
            auto *isz = llvm.eq(b, llvm.lit_word(0));

            auto fallthrough_block = get_fallthrough_block(blk);
            BasicBlock *then_lbl = get_block_lbl(fallthrough_block);

            BasicBlock *else_lbl = llvm.basic_block("else", contract);

            auto fallthrough_is_jumpdest = is_jumpdest(fallthrough_block);

            if (fallthrough_is_jumpdest) {
                stack_spill();
            }

            llvm.condbr(isz, then_lbl, else_lbl);

            llvm.insert_at(else_lbl);

            if (!fallthrough_is_jumpdest) {
                stack_spill();
            }
            emit_jump(v);
        }

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
                exit_f, {ctx_ref, llvm.lit(64, static_cast<uint64_t>(status))});
            llvm.unreachable();
        }

        template <evmc_revision Rev>
        void selfdestruct_()
        {
            if (selfdestruct_f == nullptr) {
                llvm.save_insert();

                auto *ffi = declare_symbol(
                    term_name(SelfDestruct),
                    (void *)(&selfdestruct<Rev>),
                    llvm.void_ty,
                    {llvm.ptr_ty(context_ty), llvm.ptr_ty(llvm.word_ty)});

                auto [f, arg] = llvm.internal_function_definition(
                    term_name(SelfDestruct),
                    llvm.void_ty,
                    {llvm.ptr_ty(context_ty), llvm.word_ty});
                f->addFnAttr(Attribute::NoReturn);
                auto *entry = llvm.basic_block("entry", f);
                llvm.insert_at(entry);

                auto *p = assign(arg[1]);
                llvm.call_void(ffi, {arg[0], p});
                llvm.unreachable();
                selfdestruct_f = f;
                llvm.restore_insert();
            };
            auto *addr = virtual_stack.pop();
            llvm.call_void(selfdestruct_f, {ctx_ref, addr});
            llvm.unreachable();
        };

        Function *init_ret_rev(Terminator term, StatusCode status)
        {
            llvm.save_insert();

            auto [f, arg] = llvm.internal_function_definition(
                term_name(term),
                llvm.void_ty,
                {llvm.ptr_ty(context_ty), llvm.word_ty, llvm.word_ty});
            f->addFnAttr(Attribute::NoReturn);
            auto *entry = llvm.basic_block("entry", f);
            auto *ctx_ref = arg[0];
            llvm.insert_at(entry);
            auto *offsetp = context_gep(ctx_ref, context_offset_result_offset);
            llvm.store(arg[1], offsetp);
            auto *sizep = context_gep(ctx_ref, context_offset_result_size);
            llvm.store(arg[2], sizep);
            exit_(ctx_ref, status);
            llvm.restore_insert();
            return f;
        }

        void return_()
        {
            if (return_f == nullptr) {
                return_f = init_ret_rev(Return, StatusCode::Success);
            };
            auto *a = virtual_stack.pop();
            auto *b = virtual_stack.pop();
            llvm.call_void(return_f, {ctx_ref, a, b});
            llvm.unreachable();
        };

        void revert()
        {
            if (revert_f == nullptr) {
                revert_f = init_ret_rev(Revert, StatusCode::Revert);
            };
            auto *a = virtual_stack.pop();
            auto *b = virtual_stack.pop();
            llvm.call_void(revert_f, {ctx_ref, a, b});
            llvm.unreachable();
        };

        void stop()
        {
            if (stop_f == nullptr) {
                llvm.save_insert();
                auto [f, arg] = llvm.internal_function_definition(
                    term_name(Stop), llvm.void_ty, {llvm.ptr_ty(context_ty)});
                f->addFnAttr(Attribute::NoReturn);
                auto *entry = llvm.basic_block("entry", f);
                llvm.insert_at(entry);
                exit_(arg[0], StatusCode::Success);
                stop_f = f;
                llvm.restore_insert();
            };
            llvm.call_void(stop_f, {ctx_ref});
            llvm.unreachable();
        };

        template <evmc_revision Rev>
        void terminate_block(Block const &blk)
        {
            auto term = blk.terminator;
            switch (term) {
            case Jump:
                jump();
                return;
            case JumpI:
                jumpi(blk);
                return;
            case FallThrough:
                fallthrough(blk);
                return;
            case Return:
                return_();
                return;
            case Revert:
                revert();
                return;
            case Stop:
                stop();
                return;
            case SelfDestruct:
                selfdestruct_<Rev>();
                return;
            default:
                MONAD_VM_ASSERT(term == InvalidInstruction);
                exit_(ctx_ref, StatusCode::Error);
                return;
            };
        };

        Function *init_block_begin()
        {
            std::vector<Type *> const param_tys = {
                llvm.ptr_ty(context_ty),
                llvm.int_ty(64),
                llvm.int_ty(32),
                llvm.int_ty(32),
                llvm.ptr_ty(llvm.int_ty(32)),
            };
            llvm.save_insert();
            auto [fun, arg] = llvm.internal_function_definition(
                "block_begin", llvm.void_ty, param_tys);
            auto *ctx_ref = arg[0];
            auto *min_gas = arg[1];
            auto *low = arg[2];
            auto *high = arg[3];
            auto *stack_heightp = arg[4];

            auto *entry = llvm.basic_block("entry", fun);
            auto *then_lbl = llvm.basic_block("then_lbl", fun);
            auto *else_lbl = llvm.basic_block("else_lbl", fun);
            llvm.insert_at(entry);

            auto *gas_ref = context_gep(ctx_ref, context_offset_gas_remaining);

            auto *gas = llvm.load(llvm.int_ty(64), gas_ref);
            auto *gas1 = llvm.sub(gas, min_gas);

            auto *gas_pred = llvm.slt(gas1, llvm.lit(64, 0));

            auto *stack_height = llvm.load(llvm.int_ty(32), stack_heightp);

            auto *stack_low = llvm.add(stack_height, low);
            auto *low_pred = llvm.slt(stack_low, llvm.lit(32, 0));
            auto *pred = llvm.or_(gas_pred, low_pred);

            auto *stack_high = llvm.add(stack_height, high);
            auto *high_pred = llvm.sgt(stack_high, llvm.lit(32, 1024));

            auto *pred1 = llvm.or_(pred, high_pred);

            llvm.condbr(pred1, then_lbl, else_lbl);

            llvm.insert_at(then_lbl);
            exit_(ctx_ref, StatusCode::Error);

            llvm.insert_at(else_lbl);
            llvm.store(gas1, gas_ref);
            llvm.ret_void();

            llvm.restore_insert();
            return fun;
        };

        template <evmc_revision Rev>
        bool block_begin(Block const &blk)
        {
            auto *lbl = get_block_lbl(blk);

            llvm.insert_at(lbl);

            if (is_jumpdest(blk)) {
                virtual_stack.clear();
                jumpdests.emplace_back(blk.offset, lbl);
            }

            // compute gas
            int64_t const min_gas =
                is_jumpdest(blk) ? 1 + base_gas_remaining : base_gas_remaining;

            // compute low/high stack water marks
            auto [low, high] = virtual_stack.deltas(blk);

            if (low < -1024 || // impossible to not be out of bounds
                high > 1024 ||
                (blk.terminator == Jump && ir.jump_dests().size() == 0)) {
                exit_(ctx_ref, StatusCode::Error);
                return true;
            }

            llvm.call_void(
                block_begin_f,
                {ctx_ref,
                 llvm.lit(64, static_cast<uint64_t>(min_gas)),
                 llvm.lit(32, static_cast<uint64_t>(low)),
                 llvm.lit(32, static_cast<uint64_t>(high)),
                 evm_stack_height});

            stack_unspill(low);

            return false;
        };

        BasicBlock *get_block_lbl(Block const &blk)
        {
            auto item = block_tbl.find(blk.offset);
            if (item == block_tbl.end()) {
                auto const *nm = is_jumpdest(blk) ? "jd" : "fallthrough";
                auto *lbl = llvm.basic_block(
                    std::format("{}_loc{}", nm, blk.offset), contract);
                block_tbl.insert({blk.offset, lbl});
                return lbl;
            }
            return item->second;
        };

        Value *context_gep(Value *ctx_ref, uint64_t offset)
        {
            return llvm.gep(llvm.int_ty(8), ctx_ref, {llvm.lit(64, offset)});
        };

        Value *assign(Value *v)
        {
            Value *p = llvm.alloca_(llvm.word_ty);
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
            llvm.save_insert();

            std::vector<Type *> tys;
            std::vector<Type *> ffi_tys;

            bool const has_ret = instr.increases_stack();
            bool const has_gas = has_gas_param(instr);
            size_t const n = instr.stack_args();
            std::string const nm = instr_name(instr);

            bool const has_ctx = has_ctx_param(instr);

            if (has_ctx) {
                tys.push_back(llvm.ptr_ty(context_ty));
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
                tys.push_back(llvm.int_ty(64));
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

            size_t const di = has_ctx ? 1 : 0;

            for (size_t i = 0; i < n; ++i) {
                auto *p = assign(arg[i + di]);
                vals.push_back(p);
            }

            Value *r = nullptr;

            if (has_ret) {
                r = n == 0 ? llvm.alloca_(llvm.word_ty) : vals[1];
                vals.insert(vals.begin() + static_cast<long>(di), r);
            }

            if (has_gas) {
                vals.push_back(arg[n + di]);
            }

            llvm.call_void(ffi, vals);

            if (has_ret) {
                llvm.ret(llvm.load(llvm.word_ty, r));
            }
            else {
                llvm.ret_void();
            }

            llvm.restore_insert();
            return f;
        };

        Function *load_context_addr(Instruction const &instr, uint64_t offset)
        {
            llvm.save_insert();
            auto [f, vctx] = context_fun(instr);
            auto *ref = context_gep(vctx, offset);
            auto *val = llvm.load(llvm.addr_ty, ref);
            llvm.ret(llvm.addr_to_word(val));
            llvm.restore_insert();
            return f;
        };

        Function *load_context_uint32(Instruction const &instr, uint64_t offset)
        {
            llvm.save_insert();
            auto [f, vctx] = context_fun(instr);
            auto *ref = context_gep(vctx, offset);
            auto *val = llvm.load(llvm.int_ty(32), ref);
            llvm.ret(llvm.cast_word(val));
            llvm.restore_insert();
            return f;
        };

        Function *load_context_uint64(Instruction const &instr, uint64_t offset)
        {
            llvm.save_insert();
            auto [f, vctx] = context_fun(instr);
            auto *ref = context_gep(vctx, offset);
            auto *val = llvm.load(llvm.int_ty(64), ref);
            llvm.ret(llvm.cast_word(val));
            llvm.restore_insert();
            return f;
        };

        Function *load_context_be(Instruction const &instr, uint64_t offset)
        {
            llvm.save_insert();
            auto [f, vctx] = context_fun(instr);
            auto *ref = context_gep(vctx, offset);
            auto *val = llvm.load(llvm.word_ty, ref);
            llvm.ret(llvm.bswap(val));
            llvm.restore_insert();
            return f;
        };

        std::tuple<Function *, Value *> context_fun(Instruction const &instr)
        {
            auto [f, arg] = llvm.internal_function_definition(
                instr_name(instr), llvm.word_ty, {llvm.ptr_ty(context_ty)});
            auto *entry = llvm.basic_block("entry", f);
            llvm.insert_at(entry);
            return std::make_tuple(f, arg[0]);
        };

        Function *llvm_unop(
            Instruction const &instr, Value *(LLVMState::*method)(Value *))
        {
            llvm.save_insert();
            auto [f, arg] = llvm.internal_function_definition(
                instr_name(instr), llvm.word_ty, {llvm.word_ty, llvm.word_ty});
            auto *entry = llvm.basic_block("entry", f);
            llvm.insert_at(entry);
            llvm.ret((&llvm->*method)(arg[0]));
            llvm.restore_insert();
            return f;
        }

        Function *llvm_binop(
            Instruction const &instr,
            Value *(LLVMState::*method)(Value *, Value *))
        {
            llvm.save_insert();
            auto [f, arg] = llvm.internal_function_definition(
                instr_name(instr), llvm.word_ty, {llvm.word_ty, llvm.word_ty});
            auto *entry = llvm.basic_block("entry", f);
            llvm.insert_at(entry);
            llvm.ret(llvm.cast_word((&llvm->*method)(arg[0], arg[1])));
            llvm.restore_insert();
            return f;
        }

        Function *llvm_divop(
            Instruction const &instr,
            Value *(LLVMState::*method)(Value *, Value *))
        {
            llvm.save_insert();
            auto [f, arg] = llvm.internal_function_definition(
                instr_name(instr), llvm.word_ty, {llvm.word_ty, llvm.word_ty});
            auto *entry = llvm.basic_block("entry", f);
            llvm.insert_at(entry);

            auto *isz = llvm.eq(arg[1], llvm.lit_word(0));
            auto *then_lbl = llvm.basic_block("then_lbl", f);
            auto *else_lbl = llvm.basic_block("else_lbl", f);

            llvm.condbr(isz, then_lbl, else_lbl);

            llvm.insert_at(then_lbl);
            llvm.ret(llvm.lit_word(0));

            llvm.insert_at(else_lbl);
            llvm.ret((&llvm->*method)(arg[0], arg[1]));

            llvm.restore_insert();
            return f;
        }

        Function *llvm_shiftop(
            Instruction const &instr,
            Value *(LLVMState::*method)(Value *, Value *))
        {
            llvm.save_insert();
            auto [f, arg] = llvm.internal_function_definition(
                instr_name(instr), llvm.word_ty, {llvm.word_ty, llvm.word_ty});
            auto *entry = llvm.basic_block("entry", f);
            llvm.insert_at(entry);

            auto *isgt = llvm.ugt(arg[0], llvm.lit_word(255));
            auto *then_lbl = llvm.basic_block("then_lbl", f);
            auto *else_lbl = llvm.basic_block("else_lbl", f);

            llvm.condbr(isgt, then_lbl, else_lbl);

            llvm.insert_at(then_lbl);
            llvm.ret(llvm.lit_word(0));

            llvm.insert_at(else_lbl);
            llvm.ret((&llvm->*method)(arg[1], arg[0]));

            llvm.restore_insert();
            return f;
        }

        Function *llvm_gas(Instruction const &instr)
        {
            llvm.save_insert();
            auto [f, arg] = llvm.internal_function_definition(
                instr_name(instr),
                llvm.word_ty,
                {llvm.ptr_ty(context_ty), llvm.int_ty(64)});
            auto *entry = llvm.basic_block("entry", f);
            llvm.insert_at(entry);

            auto *ref = context_gep(arg[0], context_offset_gas_remaining);
            auto *gas = llvm.load(llvm.int_ty(64), ref);
            auto *r = llvm.add(gas, arg[1]);
            llvm.ret(llvm.cast_word(r));
            llvm.restore_insert();
            return f;
        }

        Function *llvm_byte(Instruction const &instr)
        {
            llvm.save_insert();
            auto [f, arg] = llvm.internal_function_definition(
                instr_name(instr), llvm.word_ty, {llvm.word_ty, llvm.word_ty});
            auto *entry = llvm.basic_block("entry", f);
            llvm.insert_at(entry);

            auto *isgt = llvm.ugt(arg[0], llvm.lit_word(31));
            auto *then_lbl = llvm.basic_block("then_lbl", f);
            auto *else_lbl = llvm.basic_block("else_lbl", f);

            llvm.condbr(isgt, then_lbl, else_lbl);

            llvm.insert_at(then_lbl);
            llvm.ret(llvm.lit_word(0));

            llvm.insert_at(else_lbl);

            auto *nbytes = llvm.sub(llvm.lit_word(31), arg[0]);
            auto *nbits = llvm.mul(nbytes, llvm.lit_word(8));
            llvm.ret(llvm.and_(llvm.shr(arg[1], nbits), llvm.lit_word(255)));
            llvm.restore_insert();
            return f;
        }

        Function *llvm_sar(Instruction const &instr)
        {
            llvm.save_insert();
            auto [f, arg] = llvm.internal_function_definition(
                instr_name(instr), llvm.word_ty, {llvm.word_ty, llvm.word_ty});
            auto *entry = llvm.basic_block("entry", f);
            llvm.insert_at(entry);

            auto *isgt = llvm.ugt(arg[0], llvm.lit_word(255));
            auto *then_lbl = llvm.basic_block("then_lbl", f);
            auto *else_lbl = llvm.basic_block("else_lbl", f);

            llvm.condbr(isgt, then_lbl, else_lbl);

            llvm.insert_at(then_lbl);
            llvm.ret(llvm.sar(arg[1], llvm.lit_word(255)));

            llvm.insert_at(else_lbl);
            llvm.ret(llvm.sar(arg[1], arg[0]));

            llvm.restore_insert();
            return f;
        }

        Function *llvm_signextend(Instruction const &instr)
        {
            llvm.save_insert();
            auto [f, arg] = llvm.internal_function_definition(
                instr_name(instr), llvm.word_ty, {llvm.word_ty, llvm.word_ty});
            auto *entry = llvm.basic_block("entry", f);
            llvm.insert_at(entry);

            auto *isgt = llvm.ugt(arg[0], llvm.lit_word(30));
            auto *then_lbl = llvm.basic_block("then_lbl", f);
            auto *else_lbl = llvm.basic_block("else_lbl", f);

            llvm.condbr(isgt, then_lbl, else_lbl);

            llvm.insert_at(then_lbl);
            llvm.ret(arg[1]);

            llvm.insert_at(else_lbl);

            auto *nbytes = llvm.sub(llvm.lit_word(31), arg[0]);
            auto *nbits = llvm.mul(nbytes, llvm.lit_word(8));
            llvm.ret(llvm.sar(llvm.shl(arg[1], nbits), nbits));
            llvm.restore_insert();
            return f;
        }

        template <evmc_revision Rev>
        Function *init_instr(Instruction const &instr)
        {
            auto op = instr.opcode();
            switch (op) {
            case SStore:
                return ffi_runtime(instr, sstore<Rev>);

            case Create:
                return ffi_runtime(instr, create<Rev>);

            case Create2:
                return ffi_runtime(instr, create2<Rev>);

            case DelegateCall:
                return ffi_runtime(instr, delegatecall<Rev>);

            case StaticCall:
                return ffi_runtime(instr, staticcall<Rev>);

            case Call:
                return ffi_runtime(instr, call<Rev>);

            case CallCode:
                return ffi_runtime(instr, callcode<Rev>);

            case SelfBalance:
                return ffi_runtime(instr, selfbalance);

            case Balance:
                return ffi_runtime(instr, balance<Rev>);

            case ExtCodeHash:
                return ffi_runtime(instr, extcodehash<Rev>);

            case ExtCodeSize:
                return ffi_runtime(instr, extcodesize<Rev>);

            case SLoad:
                return ffi_runtime(instr, sload<Rev>);

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
                return ffi_runtime(instr, exp<Rev>);

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
                return ffi_runtime(instr, extcodecopy<Rev>);

            case AddMod:
                return ffi_runtime(instr, runtime::addmod);

            case MulMod:
                return ffi_runtime(instr, runtime::mulmod);

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
                return llvm_gas(instr);

            case Byte:
                return llvm_byte(instr);

            case SignExtend:
                return llvm_signextend(instr);

            case Div:
                return llvm_divop(instr, &LLVMState::udiv);
            case SDiv:
                return llvm_divop(instr, &LLVMState::sdiv);

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
