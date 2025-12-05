//===---------- ExprAutoMutationAnalyzer.hpp ----------------------------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
// This file was modified by Category Labs, Inc. on [Aug 21, 2025].
//
//===----------------------------------------------------------------------===//

#pragma once

#include "clang/ASTMatchers/ASTMatchers.h"
#include "llvm/ADT/DenseMap.h"
#include <memory>

namespace clang
{

    class FunctionParmMutationAnalyzer;

    /// Analyzes whether any mutative operations are applied to an expression
    /// within a given statement.
    class ExprAutoMutationAnalyzer
    {
        friend class FunctionParmMutationAnalyzer;

    public:
        struct Memoized
        {
            using ResultMap = llvm::DenseMap<Expr const *, Stmt const *>;
            using FunctionParaAnalyzerMap = llvm::SmallDenseMap<
                FunctionDecl const *,
                std::unique_ptr<FunctionParmMutationAnalyzer>>;

            ResultMap Results;
            ResultMap PointeeResults;
            FunctionParaAnalyzerMap FuncParmAnalyzer;

            void clear()
            {
                Results.clear();
                PointeeResults.clear();
                FuncParmAnalyzer.clear();
            }
        };

        struct Analyzer
        {
            Analyzer(Stmt const &Stm, ASTContext &Context, Memoized &Memorized)
                : Stm(Stm)
                , Context(Context)
                , Memorized(Memorized)
            {
            }

            Stmt const *findMutation(Expr const *Exp);
            Stmt const *findMutation(Decl const *Dec);

            Stmt const *findPointeeMutation(Expr const *Exp);
            Stmt const *findPointeeMutation(Decl const *Dec);

        private:
            using MutationFinder = Stmt const *(Analyzer::*)(Expr const *);

            Stmt const *findMutationMemoized(
                Expr const *Exp, llvm::ArrayRef<MutationFinder> Finders,
                Memoized::ResultMap &MemoizedResults);
            Stmt const *tryEachDeclRef(Decl const *Dec, MutationFinder Finder);
            Stmt const *findMaybeRemovedIfConstexpr(Decl const *Dec);

            Stmt const *
            findExprMutation(ArrayRef<ast_matchers::BoundNodes> Matches);
            Stmt const *
            findDeclMutation(ArrayRef<ast_matchers::BoundNodes> Matches);
            Stmt const *
            findExprPointeeMutation(ArrayRef<ast_matchers::BoundNodes> Matches);
            Stmt const *
            findDeclPointeeMutation(ArrayRef<ast_matchers::BoundNodes> Matches);

            Stmt const *findDirectMutation(Expr const *Exp);
            Stmt const *findMemberMutation(Expr const *Exp);
            Stmt const *findArrayElementMutation(Expr const *Exp);
            Stmt const *findCastMutation(Expr const *Exp);
            Stmt const *findRangeLoopMutation(Expr const *Exp);
            Stmt const *findReferenceMutation(Expr const *Exp);
            Stmt const *findFunctionArgMutation(Expr const *Exp);

            Stmt const &Stm;
            ASTContext &Context;
            Memoized &Memorized;
        };

        ExprAutoMutationAnalyzer(Stmt const &Stm, ASTContext &Context)
            : Memorized()
            , A(Stm, Context, Memorized)
        {
        }

        /// check whether stmt is unevaluated. mutation analyzer will ignore the
        /// content in unevaluated stmt.
        static bool isUnevaluated(const Stmt *Stm, ASTContext &Context);

        bool isMutated(Expr const *Exp)
        {
            return findMutation(Exp) != nullptr;
        }

        bool isMutated(Decl const *Dec)
        {
            return findMutation(Dec) != nullptr;
        }

        Stmt const *findMutation(Expr const *Exp)
        {
            return A.findMutation(Exp);
        }

        Stmt const *findMutation(Decl const *Dec)
        {
            return A.findMutation(Dec);
        }

        bool isPointeeMutated(Expr const *Exp)
        {
            return findPointeeMutation(Exp) != nullptr;
        }

        bool isPointeeMutated(Decl const *Dec)
        {
            return findPointeeMutation(Dec) != nullptr;
        }

        Stmt const *findPointeeMutation(Expr const *Exp)
        {
            return A.findPointeeMutation(Exp);
        }

        Stmt const *findPointeeMutation(Decl const *Dec)
        {
            return A.findPointeeMutation(Dec);
        }

    private:
        Memoized Memorized;
        Analyzer A;
    };

    // A convenient wrapper around ExprAutoMutationAnalyzer for analyzing function
    // params.
    class FunctionParmMutationAnalyzer
    {
    public:
        static FunctionParmMutationAnalyzer *getFunctionParmMutationAnalyzer(
            FunctionDecl const &Func, ASTContext &Context,
            ExprAutoMutationAnalyzer::Memoized &Memorized)
        {
            auto it = Memorized.FuncParmAnalyzer.find(&Func);
            if (it == Memorized.FuncParmAnalyzer.end()) {
                it = Memorized.FuncParmAnalyzer
                         .try_emplace(
                             &Func,
                             std::unique_ptr<FunctionParmMutationAnalyzer>(
                                 new FunctionParmMutationAnalyzer(
                                     Func, Context, Memorized)))
                         .first;
            }
            return it->getSecond().get();
        }

        bool isMutated(ParmVarDecl const *Parm)
        {
            return findMutation(Parm) != nullptr;
        }

        Stmt const *findMutation(ParmVarDecl const *Parm);

    private:
        ExprAutoMutationAnalyzer::Analyzer BodyAnalyzer;
        llvm::DenseMap<ParmVarDecl const *, Stmt const *> Results;

        FunctionParmMutationAnalyzer(
            FunctionDecl const &Func, ASTContext &Context,
            ExprAutoMutationAnalyzer::Memoized &Memorized);
    };

} // namespace clang
