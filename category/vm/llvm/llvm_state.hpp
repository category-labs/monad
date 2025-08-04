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
#include <llvm/IR/Instructions.h>
#include <llvm/IR/Intrinsics.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/Type.h>
#include <llvm/IR/Value.h>
#include <llvm/IR/Verifier.h>
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
            std::cerr << module_str;
        }

        void set_contract_addr()
        {
            JITDylib &jd = lljit->getMainJITDylib();

            MONAD_VM_ASSERT(!jd.define(absoluteSymbols(opcode_syms)));

            MONAD_VM_ASSERT(verifyModule(*llvm_module));

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

        Value *gep(Type *ty, Value *v, std::vector<Value *> const &offsets)
        {
            return ir.CreateInBoundsGEP(ty, v, offsets, "gep");
        }

        void store(Value *v, Value *p)
        {
            ir.CreateStore(v, p);
        };

        Value *load(Type *ty, Value *v)
        {
            return ir.CreateLoad(ty, v, "load");
        };

        Value *alloca_(Type *ty)
        {
            return ir.CreateAlloca(ty, nullptr, "alloca");
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

        void condbr(Value *pred, BasicBlock *then_lbl, BasicBlock *else_lbl)
        {
            ir.CreateCondBr(pred, then_lbl, else_lbl);
        };

        SwitchInst *switch_(Value *v, BasicBlock *dflt, unsigned n)
        {
            return ir.CreateSwitch(v, dflt, n);
        };

        Value *cast_word(Value *a)
        {
            return ir.CreateIntCast(a, int_ty(256), false, "cast_word");
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
            f->addFnAttr(Attribute::AlwaysInline);
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
