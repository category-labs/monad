//===--- AutoConstCorrectnessCheck.hpp - clang-tidy -------------------*- C++
//-*-===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
// This file was modified by Category Labs, Inc. on [Aug 21, 2025].
//
//===----------------------------------------------------------------------===//

#pragma once

#include "clang-tidy/ClangTidyCheck.h"
#include "ExprAutoMutationAnalyzer.hpp"
#include "llvm/ADT/DenseSet.h"

namespace clang::tidy::misc
{

    /// This check warns on variables which could be declared const but are not.
    ///
    /// For the user-facing documentation see:
    /// http://clang.llvm.org/extra/clang-tidy/checks/misc/const-correctness.html
    class AutoConstCorrectnessCheck : public ClangTidyCheck
    {
    public:
        AutoConstCorrectnessCheck(StringRef Name, ClangTidyContext *Context);

        // The rules for C and 'const' are different and incompatible for this
        // check.
        bool
        isLanguageVersionSupported(LangOptions const &LangOpts) const override
        {
            return LangOpts.CPlusPlus;
        }

        void storeOptions(ClangTidyOptions::OptionMap &Opts) override;
        void registerMatchers(ast_matchers::MatchFinder *Finder) override;
        void
        check(ast_matchers::MatchFinder::MatchResult const &Result) override;

    private:
        void registerScope(Stmt const *LocalScope, ASTContext *Context);

        using MutationAnalyzer = std::unique_ptr<ExprAutoMutationAnalyzer>;
        llvm::DenseMap<Stmt const *, MutationAnalyzer> ScopesCache;
        llvm::DenseSet<SourceLocation> TemplateDiagnosticsCache;

        bool const AnalyzeValues;
        bool const AnalyzeReferences;
        bool const WarnPointersAsValues;

        bool const TransformValues;
        bool const TransformReferences;
        bool const TransformPointersAsValues;
    };

} // namespace clang::tidy::misc
