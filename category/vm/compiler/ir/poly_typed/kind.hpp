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

#include <category/vm/compiler/transactional_unordered_map.hpp>

#include <format>
#include <memory>
#include <variant>
#include <vector>

namespace monad::vm::compiler::poly_typed
{
    using VarName = uint64_t;

    struct Word;
    struct Any;
    struct KindVar;
    struct LiteralVar;
    struct WordCont;
    struct Cont;

    using PreKind =
        std::variant<Word, Any, KindVar, LiteralVar, WordCont, Cont>;

    using Kind = std::shared_ptr<PreKind>;

    struct ContVar
    {
        VarName var;
    };

    struct ContWords
    {
    };

    using ContTailKind = std::variant<ContVar, ContWords>;

    struct PreContKind
    {
        std::vector<Kind> front;
        ContTailKind tail;
    };

    using ContKind = std::shared_ptr<PreContKind>;

    extern ContKind cont_words;

    ContKind cont_kind(std::vector<Kind> kinds, ContTailKind t);

    ContKind cont_kind(std::vector<Kind> kinds, VarName v);

    ContKind cont_kind(std::vector<Kind> kinds);

    struct Word
    {
    };

    extern Kind word;

    struct Any
    {
    };

    extern Kind any;

    struct KindVar
    {
        VarName var;
    };

    Kind kind_var(VarName);

    struct LiteralVar
    {
        VarName var;
        ContKind cont;
    };

    Kind literal_var(VarName, ContKind);

    struct WordCont
    {
        ContKind cont;
    };

    Kind word_cont(ContKind);

    struct Cont
    {
        ContKind cont;
    };

    Kind cont(ContKind);

    struct PolyVarSubstMap
    {
        std::unordered_map<VarName, VarName> kind_map;
        std::unordered_map<VarName, VarName> cont_map;
    };

    enum class LiteralType
    {
        Word,
        Cont,
        WordCont
    };

    inline bool operator==(LiteralType t1, LiteralType t2)
    {
        return static_cast<int>(t1) == static_cast<int>(t2);
    }

    inline bool operator!=(LiteralType t1, LiteralType t2)
    {
        return !(t1 == t2);
    }

    void
    format_kind(Kind const &kind, std::format_context &ctx, bool use_parens);

    void format_cont(ContKind const &cont, std::format_context &ctx);

    /// Equality up to renaming of variables.
    /// Does not consider Word.. to be equal to Word,Word..
    bool alpha_equal(Kind, Kind);

    bool operator==(Kind, Kind) = delete;
    bool operator!=(Kind, Kind) = delete;

    /// Equality where Word.. is equal to Word,Word..
    bool weak_equal(Kind, Kind);

    /// Whether there exists a `SubstMap su`, such that `su.subst(generic) ==
    /// specific`. The function considers Word.. to be equal to Word,Word..
    bool can_specialize(Kind generic, Kind specific);

    /// Equality up to renaming of variables.
    /// Does not consider Word.. to be equal to Word,Word..
    bool alpha_equal(ContKind, ContKind);

    bool operator==(ContKind, ContKind) = delete;
    bool operator!=(ContKind, ContKind) = delete;

    /// Equality where Word.. is equal to Word,Word..
    bool weak_equal(ContKind, ContKind);

    /// Whether there exists a `SubstMap su`, such that `su.subst(generic) ==
    /// specific`. The function considers Word.. to be equal to Word,Word..
    bool can_specialize(ContKind generic, ContKind specific);
}

template <>
struct std::formatter<monad::vm::compiler::poly_typed::Kind>
{
    constexpr auto parse(std::format_parse_context &ctx)
    {
        return ctx.begin();
    }

    auto format(
        monad::vm::compiler::poly_typed::Kind const &kind,
        std::format_context &ctx) const
    {
        monad::vm::compiler::poly_typed::format_kind(kind, ctx, false);
        return ctx.out();
    }
};

template <>
struct std::formatter<monad::vm::compiler::poly_typed::ContKind>
{
    constexpr auto parse(std::format_parse_context &ctx)
    {
        return ctx.begin();
    }

    auto format(
        monad::vm::compiler::poly_typed::ContKind const &kind,
        std::format_context &ctx) const
    {
        monad::vm::compiler::poly_typed::format_cont(kind, ctx);
        return ctx.out();
    }
};
