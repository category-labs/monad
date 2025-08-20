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

#include <category/vm/core/assert.h>
#include <category/vm/runtime/uint256.hpp>

#include <llvm/ADT/APInt.h>
#include <llvm/ADT/ArrayRef.h>
#include <llvm/ExecutionEngine/ExecutionEngine.h>
#include <llvm/ExecutionEngine/JITSymbol.h>
#include <llvm/ExecutionEngine/Orc/Core.h>
#include <llvm/ExecutionEngine/Orc/LLJIT.h>
#include <llvm/ExecutionEngine/Orc/Mangling.h>
#include <llvm/ExecutionEngine/Orc/ObjectTransformLayer.h>
#include <llvm/ExecutionEngine/Orc/Shared/ExecutorAddress.h>
#include <llvm/ExecutionEngine/Orc/Shared/ExecutorSymbolDef.h>
#include <llvm/ExecutionEngine/Orc/ThreadSafeModule.h>
#include <llvm/IR/Attributes.h>
#include <llvm/IR/BasicBlock.h>
#include <llvm/IR/Constants.h>
#include <llvm/IR/DerivedTypes.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/GlobalValue.h>
#include <llvm/IR/GlobalVariable.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/MDBuilder.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/Intrinsics.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/PassManager.h>
#include <llvm/IR/Type.h>
#include <llvm/IR/Value.h>
#include <llvm/IR/Verifier.h>
#include <llvm/Passes/PassBuilder.h>
#include <llvm/Support/Error.h>
#include <llvm/Support/raw_ostream.h>

#include <fstream>
#include <iostream>

namespace monad::vm::llvm
{
    using namespace ::llvm::orc;
    using namespace ::llvm;
    using namespace monad::vm::runtime;

    struct LLVMState
    {
    public:
        void dump_module(std::string const &nm)
        {
            std::string module_str;
            raw_string_ostream OS(module_str);
            OS << *llvm_module;
            OS.flush();
            std::ofstream out(nm);
            out << module_str;
            out.close();
        }

        void set_contract_addr(std::string const &dbg_nm = "")
        {
            LoopAnalysisManager LAM;
            FunctionAnalysisManager FAM;
            CGSCCAnalysisManager CGAM;
            ModuleAnalysisManager MAM;

            PassBuilder PB;

            PB.registerModuleAnalyses(MAM);
            PB.registerCGSCCAnalyses(CGAM);
            PB.registerFunctionAnalyses(FAM);
            PB.registerLoopAnalyses(LAM);
            PB.crossRegisterProxies(LAM, FAM, CGAM, MAM);

            ModulePassManager MPM =
                PB.buildPerModuleDefaultPipeline(OptimizationLevel::O3);

            bool const do_optimize = true;

            if (do_optimize) {
                MPM.run(*llvm_module, MAM);
            }

            if (dbg_nm != "") {
                if (do_optimize) {
                    dump_module(dbg_nm + "_opt.ll");
                }
                std::string const nm = dbg_nm + ".jit";
                ObjectTransformLayer &otl = lljit->getObjTransformLayer();
                DumpObjects const dumpobjs = DumpObjects("", nm);
                otl.setTransform(dumpobjs);
            }

            JITDylib &jd = lljit->getMainJITDylib();

            MONAD_VM_ASSERT(!jd.define(absoluteSymbols(opcode_syms)));

            if (!do_optimize) {
                MONAD_VM_ASSERT(
                    verifyModule(*llvm_module)); // BAL: this fails when O2 and
                                                 // O3 are applied.  Why?
            }

            ThreadSafeModule tsm(
                std::move(llvm_module), std::move(llvm_context));

            ExitOnErr(lljit->addIRModule(std::move(tsm)));

            MONAD_VM_ASSERT(lljit);

            Expected<ExecutorAddr> expected_contract_addr =
                lljit->lookup("contract");

            if (auto err = expected_contract_addr.takeError()) {
                errs() << "error:" << toString(std::move(err)) << '\n';
                MONAD_VM_ASSERT(false);
            }

            contract_addr = reinterpret_cast<void (*)()>(
                expected_contract_addr->getValue());
        };

        void unreachable()
        {
            ir.CreateUnreachable();
            ret_void();
        };

        void ret(Value *r)
        {
            ir.CreateRet(r);
        };

        void ret_void()
        {
            ir.CreateRetVoid();
        };

        void call_void(Function *f, std::vector<Value *> const &args)
        {
            ir.CreateCall(f, args);
        };

        Value *call(Function *f, std::vector<Value *> const &args)
        {
            return ir.CreateCall(f, args, "call");
        };

        void insert_symbol(std::string const &nm, void const *f)
        {
            JITTargetAddress const jit_addr = pointerToJITTargetAddress(f);
            auto esd = ExecutorSymbolDef(
                ExecutorAddr(jit_addr), JITSymbolFlags::Callable);
            opcode_syms.insert({mangle(nm), esd});
        }

        void save_insert()
        {
            auto *lbl = ir.GetInsertBlock();
            insert_lbls.push_back(lbl);
        };

        void insert_at(BasicBlock *blk)
        {
            ir.SetInsertPoint(blk);
        };

        void restore_insert()
        {
            MONAD_VM_ASSERT(insert_lbls.size() > 0);
            insert_at(insert_lbls.back());
            insert_lbls.pop_back();
        };

        Value *gep(Type *ty, Value *v, ArrayRef<Value *> offsets, std::string_view nm)
        {
            return ir.CreateInBoundsGEP(ty, v, offsets, nm);
        }

        void store(Value *v, Value *p)
        {
            ir.CreateStore(v, p);
        };

        Value *load(Type *ty, Value *v)
        {
            return ir.CreateLoad(ty, v, "load");
        };

        Value *alloca_(Type *ty, std::string_view nm)
        {
            return ir.CreateAlloca(ty, nullptr, nm);
        }

        void br(BasicBlock *blk)
        {
            ir.CreateBr(blk);
        };

        Value *bswap(Value *val)
        {
            if (bswap_f == nullptr) {
                bswap_f = ::llvm::Intrinsic::getDeclaration(
                    &m, ::llvm::Intrinsic::bswap, {word_ty});
            }
            return call(bswap_f, {val});
        };

        Value *addr_to_word(Value *val)
        {
            return shr(bswap(cast_word(val)), lit_word(96));
        };

        void condbr(Value *pred, BasicBlock *then_lbl, BasicBlock *else_lbl, bool predict_true)
        {
        MDNode *weights;
        if (predict_true)
        {
            weights = MDBuilder(context).createLikelyBranchWeights();
        } else {
            weights = MDBuilder(context).createUnlikelyBranchWeights();
        }
            ir.CreateCondBr(pred, then_lbl, else_lbl, weights);
        };

        SwitchInst *switch_(Value *v, BasicBlock *dflt, unsigned n)
        {
            return ir.CreateSwitch(v, dflt, n);
        };

        Value *cast_word(Value *a)
        {
            return ir.CreateIntCast(a, int_ty(256), false, "cast_word");
        };

        Value *cast_bool(Value *a)
        {
            return ir.CreateIntCast(a, int_ty(1), false, "cast_bool");
        };

        Value *cast_u32(Value *a)
        {
            return ir.CreateIntCast(a, int_ty(32), false, "cast_u32");
        };

        Value *not_(Value *a)
        {
            return ir.CreateNot(a, "not");
        };

        Value *shl(Value *a, Value *b)
        {
            return ir.CreateShl(a, b, "shl");
        };

        Value *shr(Value *a, Value *b)
        {
            return ir.CreateLShr(a, b, "shr");
        };

        Value *sar(Value *a, Value *b)
        {
            return ir.CreateAShr(a, b, "sar");
        };

        Value *udiv(Value *a, Value *b)
        {
            return ir.CreateUDiv(a, b, "udiv");
        };

        Value *sdiv(Value *a, Value *b)
        {
            return ir.CreateSDiv(a, b, "sdiv");
        };

        Value *urem(Value *a, Value *b)
        {
            return ir.CreateURem(a, b, "urem");
        };

        Value *srem(Value *a, Value *b)
        {
            return ir.CreateSRem(a, b, "srem");
        };

        Value *mul(Value *a, Value *b)
        {
            return ir.CreateMul(a, b, "mul");
        };

        Value *add(Value *a, Value *b)
        {
            return ir.CreateAdd(a, b, "add");
        };

        Value *addmod(Value *a, Value *b, Value *n)
        {
            auto *a1 = ir.CreateIntCast(a, int_ty(257), false);
            auto *b1 = ir.CreateIntCast(b, int_ty(257), false);
            auto *n1 = ir.CreateIntCast(n, int_ty(257), false);
            auto *r = urem(add(a1, b1), n1);
            return ir.CreateIntCast(r, int_ty(256), false);
        };

        Value *mulmod(Value *a, Value *b, Value *n)
        {
            auto *a1 = ir.CreateIntCast(a, int_ty(512), false);
            auto *b1 = ir.CreateIntCast(b, int_ty(512), false);
            auto *n1 = ir.CreateIntCast(n, int_ty(512), false);
            auto *r = urem(mul(a1, b1), n1);
            return ir.CreateIntCast(r, int_ty(256), false);
        };

        Value *sub(Value *a, Value *b)
        {
            return ir.CreateSub(a, b, "sub");
        };

        Value *eq(Value *a, Value *b)
        {
            return ir.CreateICmpEQ(a, b, "eq");
        };

        Value *equ(Value *a, Value *b)
        {
            return cast_word(ir.CreateICmpEQ(a, b, "equ"));
        };

        Value *is_zero(Value *a)
        {
            return equ(lit_word(0), a);
        };

        Value *xor_(Value *a, Value *b)
        {
            return ir.CreateXor(a, b, "xor");
        };

        Value *and_(Value *a, Value *b)
        {
            return ir.CreateAnd(a, b, "and");
        };

        Value *or_(Value *a, Value *b)
        {
            return ir.CreateOr(a, b, "or");
        };

    Value *select(Value *a, Value *b, Value *c)
    {
        return ir.CreateSelect(a, b, c);
    };

        Value *sgt(Value *a, Value *b)
        {
            return ir.CreateICmpSGT(a, b, "sgt");
        };

        Value *slt(Value *a, Value *b)
        {
            return ir.CreateICmpSLT(a, b, "slt");
        };

        Value *ugt(Value *a, Value *b)
        {
            return ir.CreateICmpUGT(a, b, "ugt");
        };

        Value *ult(Value *a, Value *b)
        {
            return ir.CreateICmpULT(a, b, "ult");
        };

        Type *int_ty(unsigned int sz)
        {
            return ir.getIntNTy(sz);
        };

        Type *ptr_ty(Type *ty)
        {
            return PointerType::getUnqual(ty);
        };

        ArrayType *array_ty(Type *ty, size_t sz)
        {
            return ArrayType::get(ty, sz);
        };

        Constant *lit(unsigned int sz, uint64_t x)
        {
            return ConstantInt::get(int_ty(sz), x);
        };

        ConstantInt *lit_word(uint256_t x)
        {
            std::array<uint64_t, 4> const words{
                x[0],
                x[1],
                x[2],
                x[3],
            };
            return ConstantInt::get(context, APInt(256, words));
        };

        Function *declare_function(
            std::string_view nm, Type *ty, std::vector<Type *> const &tys,
            bool is_external)
        {
            auto linkage = is_external ? Function::ExternalLinkage
                                       : Function::InternalLinkage;
            auto *fty = FunctionType::get(ty, tys, false);
            return Function::Create(fty, linkage, nm, m);
        }

        std::vector<Value *>
        function_definition_params(Function *f, std::vector<Type *> const &tys)
        {
            std::vector<Value *> params;
            auto args = f->args();
            auto *arg_iter = args.begin();

            for (size_t i = 0; i < tys.size(); ++i) {
                Argument *a = arg_iter++;
                params.push_back(a);
            }

            return params;
        }

        std::tuple<Function *, std::vector<Value *>>
        internal_function_definition(
            std::string_view nm, Type *ty, std::vector<Type *> const &tys)
        {
            Function *f = declare_function(nm, ty, tys, false);
            auto params = function_definition_params(f, tys);

            return std::make_tuple(f, params);
        }

        std::tuple<Function *, std::vector<Value *>>
        external_function_definition(
            std::string_view nm, Type *ty, std::vector<Type *> const &tys)
        {
            Function *f = declare_function(nm, ty, tys, true);
            auto params = function_definition_params(f, tys);
            return std::make_tuple(f, params);
        }

        BasicBlock *basic_block(std::string_view nm, Function *fun)
        {
            return BasicBlock::Create(context, nm, fun);
        };

    GlobalVariable *const_array(const std::vector<Constant *> vals, std::string_view nm)
    {
        MONAD_VM_ASSERT(vals.size() > 0);

        Type *ty = vals[0]->getType();
        ArrayType *arr_ty = array_ty(ty, vals.size());
        Constant *arr = ConstantArray::get(arr_ty, vals);
return new GlobalVariable(m, arr_ty, true, GlobalValue::InternalLinkage, arr, nm);
    }

    BlockAddress* block_address(BasicBlock *blk)
    {
        return BlockAddress::get(blk);
    }

    IndirectBrInst *indirectbr(Value *addr, std::vector<BasicBlock *>blks)
    {
        auto *r = ir.CreateIndirectBr(addr, static_cast<unsigned int>(blks.size()));
        for (BasicBlock *blk : blks) {
        r->addDestination(blk);
        }
        return r;
    }

    private:
        std::unique_ptr<LLVMContext> llvm_context =
            std::make_unique<LLVMContext>();
        LLVMContext &context = *llvm_context;
        IRBuilder<> ir = IRBuilder<>(context);

        // Contract Module

        std::unique_ptr<Module> llvm_module =
            std::make_unique<Module>("contract_module", context);

        Module &m = *llvm_module;

        ExitOnError const ExitOnErr;

        // create JIT
        std::unique_ptr<LLJIT> lljit = ExitOnErr(LLJITBuilder().create());

        ExecutionSession &es = lljit->getExecutionSession();
        DataLayout const &dl = lljit->getDataLayout();

        MangleAndInterner mangle = MangleAndInterner(es, dl);

        Function *bswap_f = nullptr;

        std::vector<BasicBlock *> insert_lbls;
        SymbolMap opcode_syms;

    public:
        void (*contract_addr)() = nullptr;

        Type *word_ty = int_ty(256);
        Type *addr_ty = int_ty(160);
        Type *void_ty = ir.getVoidTy();
    };
}
