//===--- MiscUpdateModule.cpp - clang-tidy -----------------*- C++
//-*-===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
// This file was modified by Category Labs, Inc. on [Sep 2, 2025].
//
//===----------------------------------------------------------------------===//

#include "clang-tidy/ClangTidyModule.h"
#include "clang-tidy/ClangTidyModuleRegistry.h"
#include "AutoConstCorrectnessCheck.hpp"

namespace clang::tidy::misc
{
    class MiscUpdateModule : public ClangTidyModule
    {
    public:
        void addCheckFactories(ClangTidyCheckFactories &CheckFactories) override
        {
            CheckFactories.registerCheck<AutoConstCorrectnessCheck>(
                "misc-auto-const-correctness");
        }
    };
} // namespace clang::tidy::misc

namespace clang::tidy
{

    // Register the module using this statically initialized variable.
    static ClangTidyModuleRegistry::Add<misc::MiscUpdateModule>
        miscUpdateInit("misc-update-module", "Updates misc checks.");

    // This anchor is used to force the linker to link in the generated object
    // file and thus register the module.
    int volatile MiscUpdateModuleAnchorSource = 0;

} // namespace clang::tidy
