//===--- ArgConstCorrectnessCheck.cpp - clang-tidy -----------------*- C++
//-*-===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
// This file was modified by Category Labs, Inc. on [Sep 2, 2025].
//
//===----------------------------------------------------------------------===//

#include "ArgConstCorrectnessCheck.hpp"
#include "clang-tidy/ClangTidyModule.h"
#include "clang-tidy/ClangTidyModuleRegistry.h"
#include "clang-tidy/utils/FixItHintUtils.h"
#include "clang/AST/ASTContext.h"
#include "clang/ASTMatchers/ASTMatchFinder.h"
#include "clang/ASTMatchers/ASTMatchers.h"

using namespace clang::ast_matchers;

namespace clang::tidy::misc
{

    namespace
    {
        // FIXME: This matcher exists in some other code-review as well.
        // It should probably move to ASTMatchers.
        AST_MATCHER(VarDecl, isLocal)
        {
            return Node.isLocalVarDecl();
        }

        AST_MATCHER_P(
            DeclStmt, containsAnyDeclaration,
            ast_matchers::internal::Matcher<Decl>, InnerMatcher)
        {
            return ast_matchers::internal::matchesFirstInPointerRange(
                       InnerMatcher,
                       Node.decl_begin(),
                       Node.decl_end(),
                       Finder,
                       Builder) != Node.decl_end();
        }

        AST_MATCHER(ReferenceType, isSpelledAsLValue)
        {
            return Node.isSpelledAsLValue();
        }

        AST_MATCHER(Type, isDependentType)
        {
            return Node.isDependentType();
        }

        AST_MATCHER_P(FunctionDecl, hasParameters,
            ast_matchers::internal::Matcher<ParmVarDecl>, InnerMatcher)
        {
            ArrayRef<ParmVarDecl*> Parameters = Node.parameters();
            clang::ast_matchers::internal::BoundNodesTreeBuilder Result;
            bool Matched = false;
            for (const auto Parameter : Parameters) {
                clang::ast_matchers::internal::BoundNodesTreeBuilder ParameterBuilder(*Builder);
                if (InnerMatcher.matches(*Parameter, Finder, &ParameterBuilder)) {
                    Matched = true;
                    Result.addMatch(ParameterBuilder);
                }
            }
            *Builder = std::move(Result);
            return Matched;
        }
    } // namespace

    ArgConstCorrectnessCheck::ArgConstCorrectnessCheck(
        StringRef Name, ClangTidyContext *Context)
        : ClangTidyCheck(Name, Context)
        , AnalyzeValues(Options.get("AnalyzeValues", true))
        , AnalyzeReferences(Options.get("AnalyzeReferences", true))
        , WarnPointersAsValues(Options.get("WarnPointersAsValues", false))
    {
        if (AnalyzeValues == false && AnalyzeReferences == false) {
            this->configurationDiag(
                "The check 'misc-arg-const-correctness' will not "
                "perform any analysis because both 'AnalyzeValues' and "
                "'AnalyzeReferences' are false.");
        }
    }

    void
    ArgConstCorrectnessCheck::storeOptions(ClangTidyOptions::OptionMap &Opts)
    {
        Options.store(Opts, "AnalyzeValues", AnalyzeValues);
        Options.store(Opts, "AnalyzeReferences", AnalyzeReferences);
        Options.store(Opts, "WarnPointersAsValues", WarnPointersAsValues);
    }

    void ArgConstCorrectnessCheck::registerMatchers(MatchFinder *Finder)
    {
        auto const ConstType = hasType(isConstQualified());
        auto const ConstReference = hasType(references(isConstQualified()));
        auto const RValueReference = hasType(referenceType(
            anyOf(rValueReferenceType(), unless(isSpelledAsLValue()))));

        auto const TemplateType = anyOf(
            hasType(hasCanonicalType(templateTypeParmType())),
            hasType(substTemplateTypeParmType()),
            hasType(isDependentType()),
            // References to template types, their substitutions or typedefs to
            // template types need to be considered as well.
            hasType(referenceType(
                pointee(hasCanonicalType(templateTypeParmType())))),
            hasType(referenceType(pointee(substTemplateTypeParmType()))));

        auto const FunctionPointerRef =
            hasType(hasCanonicalType(referenceType(pointee(functionType()))));

        auto const CandidateParameterDecl = parmVarDecl(
            unless(anyOf(
                       ConstType,
                       ConstReference,
                       TemplateType,
                       hasInitializer(isInstantiationDependent()),
                       RValueReference,
                       FunctionPointerRef,
                       hasType(cxxRecordDecl(isLambda())),
                       isImplicit())));

        // Match the function scope for which the analysis of all local
        // variables shall be run.
        auto const FunctionScope =
            functionDecl(
                hasName("try_insert_varcode"),
                hasBody(compoundStmt().bind("scope")),
                hasParameters(CandidateParameterDecl.bind("parameter")))
            .bind("function-decl");

        Finder->addMatcher(FunctionScope, this);
    }

    /// Classify for a variable in what the Const-Check is interested.
    enum class VariableCategory
    {
        Value,
        Reference,
        Pointer
    };

    void
    ArgConstCorrectnessCheck::check(MatchFinder::MatchResult const &Result)
    {
        llvm::errs() << "hello\n";
        auto const *LocalScope = Result.Nodes.getNodeAs<Stmt>("scope");
        auto const *Parameter = Result.Nodes.getNodeAs<ParmVarDecl>("parameter");
        auto const *Function =
            Result.Nodes.getNodeAs<FunctionDecl>("function-decl");

        /// If the variable was declared in a template it might be analyzed
        /// multiple times. Only one of those instantiations shall emit a
        /// warning. NOTE: This shall only deduplicate warnings for variables
        /// that are not instantiation dependent. Variables like 'int x = 42;'
        /// in a template that can become const emit multiple warnings
        /// otherwise.
        bool IsNormalVariableInTemplate = Function->isTemplateInstantiation();
        if (IsNormalVariableInTemplate &&
            TemplateDiagnosticsCache.contains(Parameter->getBeginLoc())) {
            return;
        }

        VariableCategory VC = VariableCategory::Value;
        if (Parameter->getType()->isReferenceType()) {
            VC = VariableCategory::Reference;
        }
        if (Parameter->getType()->isPointerType()) {
            VC = VariableCategory::Pointer;
        }
        if (Parameter->getType()->isArrayType()) {
            if (auto const *ArrayT = dyn_cast<ArrayType>(Parameter->getType())) {
                if (ArrayT->getElementType()->isPointerType()) {
                    VC = VariableCategory::Pointer;
                }
            }
        }

        // Each variable can only be in one category: Value, Pointer, Reference.
        // Analysis can be controlled for every category.
        if (VC == VariableCategory::Reference && !AnalyzeReferences) {
            return;
        }

        if (VC == VariableCategory::Reference &&
            Parameter->getType()->getPointeeType()->isPointerType() &&
            !WarnPointersAsValues) {
            return;
        }

        if (VC == VariableCategory::Pointer && !WarnPointersAsValues) {
            return;
        }

        if (VC == VariableCategory::Value && !AnalyzeValues) {
            return;
        }

        // The scope is only registered if the analysis shall be run.
        registerScope(LocalScope, Result.Context);

        // Offload const-analysis to utility function.
        if (ScopesCache[LocalScope]->isMutated(Parameter)) {
            return;
        }

        auto Diag = diag(
                        Parameter->getBeginLoc(),
                        "parameter %0 of type %1 can be declared 'const'")
                    << Parameter << Parameter->getType();
        if (IsNormalVariableInTemplate) {
            TemplateDiagnosticsCache.insert(Parameter->getBeginLoc());
        }
    }

    void ArgConstCorrectnessCheck::registerScope(
        Stmt const *LocalScope, ASTContext *Context)
    {
        auto &Analyzer = ScopesCache[LocalScope];
        if (!Analyzer) {
            Analyzer =
                std::make_unique<ExprAutoMutationAnalyzer>(*LocalScope, *Context);
        }
    }

} // namespace clang::tidy::misc
