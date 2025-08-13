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

#include <category/vm/compiler/ir/poly_typed/kind.hpp>
#include <category/vm/core/assert.h>
#include <category/vm/core/cases.hpp>

#include <algorithm>
#include <cstddef>
#include <format>
#include <memory>
#include <unordered_map>
#include <utility>
#include <variant>
#include <vector>

namespace
{
    using namespace monad::vm::compiler;
    using namespace monad::vm::compiler::poly_typed;

    bool
    cont_alpha_eq(PolyVarSubstMap &, ContKind, PolyVarSubstMap &, ContKind);

    bool
    kind_alpha_eq(PolyVarSubstMap &su1, Kind k1, PolyVarSubstMap &su2, Kind k2)
    {
        using monad::vm::Cases;

        if (k1->index() != k2->index()) {
            return false;
        }
        return std::visit(
            Cases{
                [](Word const &) { return true; },
                [](Any const &) { return true; },
                [&su1, &su2, &k2](KindVar const &kv1) {
                    KindVar const &kv2 = std::get<KindVar>(*k2);
                    auto it1 = su1.kind_map.find(kv1.var);
                    auto it2 = su2.kind_map.find(kv2.var);
                    if (it1 == su1.kind_map.end() &&
                        it2 == su2.kind_map.end()) {
                        su1.kind_map.insert_or_assign(kv1.var, kv2.var);
                        su2.kind_map.insert_or_assign(kv2.var, kv2.var);
                        return true;
                    }
                    else if (
                        it1 == su1.kind_map.end() ||
                        it2 == su2.kind_map.end()) {
                        return false;
                    }
                    return it1->second == it2->second;
                },
                [&su1, &su2, &k2](LiteralVar const &lv1) {
                    LiteralVar const &lv2 = std::get<LiteralVar>(*k2);
                    if (lv1.var != lv2.var) {
                        return false;
                    }
                    return cont_alpha_eq(su1, lv1.cont, su2, lv2.cont);
                },
                [&su1, &su2, &k2](WordCont const &wc1) {
                    WordCont const &wc2 = std::get<WordCont>(*k2);
                    return cont_alpha_eq(su1, wc1.cont, su2, wc2.cont);
                },
                [&su1, &su2, &k2](Cont const &c1) {
                    Cont const &c2 = std::get<Cont>(*k2);
                    return cont_alpha_eq(su1, c1.cont, su2, c2.cont);
                }},
            *k1);
    }

    bool cont_alpha_eq(
        PolyVarSubstMap &su1, ContKind c1, PolyVarSubstMap &su2, ContKind c2)
    {
        using monad::vm::Cases;

        if (c1->front.size() != c2->front.size()) {
            return false;
        }
        for (size_t i = 0; i < c1->front.size(); ++i) {
            if (!kind_alpha_eq(su1, c1->front[i], su2, c2->front[i])) {
                return false;
            }
        }
        if (c1->tail.index() != c2->tail.index()) {
            return false;
        }
        return std::visit(
            Cases{
                [&su1, &su2, &c2](ContVar const &cv1) {
                    ContVar const &cv2 = std::get<ContVar>(c2->tail);
                    auto it1 = su1.cont_map.find(cv1.var);
                    auto it2 = su2.cont_map.find(cv2.var);
                    if (it1 == su1.cont_map.end() &&
                        it2 == su2.cont_map.end()) {
                        su1.cont_map.insert_or_assign(cv1.var, cv2.var);
                        su2.cont_map.insert_or_assign(cv2.var, cv2.var);
                        return true;
                    }
                    else if (
                        it1 == su1.cont_map.end() ||
                        it2 == su2.cont_map.end()) {
                        return false;
                    }
                    return it1->second == it2->second;
                },
                [](ContWords const &) { return true; }},
            c1->tail);
    }

    struct SpecializeSubstMap
    {
        std::unordered_map<VarName, Kind> kind_map;
        std::unordered_map<VarName, ContKind> cont_map;
    };

    bool
    can_specialize(SpecializeSubstMap &su, ContKind generic, ContKind specific);

    bool can_specialize(SpecializeSubstMap &su, Kind generic, Kind specific)
    {
        using monad::vm::Cases;

        if (std::holds_alternative<KindVar>(*generic)) {
            auto new_k = su.kind_map.find(std::get<KindVar>(*generic).var);
            if (new_k != su.kind_map.end()) {
                return weak_equal(new_k->second, specific);
            }
        }
        return std::visit(
            Cases{
                [&](Word const &) {
                    return std::holds_alternative<Word>(*specific);
                },
                [&](Any const &) {
                    return std::holds_alternative<Any>(*specific);
                },
                [&](KindVar const &kv) {
                    su.kind_map.insert_or_assign(kv.var, std::move(specific));
                    return true;
                },
                [&](LiteralVar const &lv) {
                    if (!std::holds_alternative<LiteralVar>(*specific)) {
                        return false;
                    }
                    return can_specialize(
                        su, lv.cont, std::get<LiteralVar>(*specific).cont);
                },
                [&](WordCont const &wc) {
                    if (!std::holds_alternative<WordCont>(*specific)) {
                        return false;
                    }
                    return can_specialize(
                        su, wc.cont, std::get<WordCont>(*specific).cont);
                },
                [&](Cont const &c) {
                    if (!std::holds_alternative<Cont>(*specific)) {
                        return false;
                    }
                    return can_specialize(
                        su, c.cont, std::get<Cont>(*specific).cont);
                }},
            *generic);
    }

    bool
    can_specialize(SpecializeSubstMap &su, ContKind generic, ContKind specific)
    {
        size_t const min_size =
            std::min(generic->front.size(), specific->front.size());
        for (size_t i = 0; i < min_size; ++i) {
            if (!can_specialize(su, generic->front[i], specific->front[i])) {
                return false;
            }
        }
        if (std::holds_alternative<ContWords>(generic->tail)) {
            if (!std::holds_alternative<ContWords>(specific->tail)) {
                return false;
            }
            for (size_t i = min_size; i < generic->front.size(); ++i) {
                if (!can_specialize(generic->front[i], word)) {
                    return false;
                }
            }
            for (size_t i = min_size; i < specific->front.size(); ++i) {
                if (!std::holds_alternative<Word>(*specific->front[i])) {
                    return false;
                }
            }
            return true;
        }
        else if (std::holds_alternative<ContWords>(specific->tail)) {
            for (size_t i = min_size; i < generic->front.size(); ++i) {
                if (!can_specialize(generic->front[i], word)) {
                    return false;
                }
            }
            VarName const v = std::get<ContVar>(generic->tail).var;
            auto it = su.cont_map.find(v);
            if (it != su.cont_map.end()) {
                ContKind const c = it->second;
                if (!std::holds_alternative<ContWords>(c->tail)) {
                    return false;
                }
                size_t const n = std::min(
                    specific->front.size() - min_size, c->front.size());
                for (size_t i = 0; i < n; ++i) {
                    if (!weak_equal(
                            specific->front[min_size + i], c->front[i])) {
                        return false;
                    }
                }
                for (size_t i = n; i < c->front.size(); ++i) {
                    if (!std::holds_alternative<Word>(*c->front[i])) {
                        return false;
                    }
                }
                for (size_t i = min_size + n; i < specific->front.size(); ++i) {
                    if (!std::holds_alternative<Word>(*specific->front[i])) {
                        return false;
                    }
                }
            }
            else {
                std::vector<Kind> front;
                for (size_t i = min_size; i < specific->front.size(); ++i) {
                    front.push_back(specific->front[i]);
                }
                su.cont_map.insert_or_assign(v, cont_kind(std::move(front)));
            }
            return true;
        }
        else {
            if (generic->front.size() > specific->front.size()) {
                return false;
            }
            MONAD_VM_DEBUG_ASSERT(min_size == generic->front.size());
            VarName const v = std::get<ContVar>(generic->tail).var;
            auto it = su.cont_map.find(v);
            if (it != su.cont_map.end()) {
                ContKind const c = it->second;
                if (c->front.size() != specific->front.size() - min_size) {
                    return false;
                }
                for (size_t i = 0; i < c->front.size(); ++i) {
                    if (!weak_equal(
                            specific->front[min_size + i], c->front[i])) {
                        return false;
                    }
                }
                if (std::holds_alternative<ContWords>(c->tail)) {
                    return false;
                }
                if (std::get<ContVar>(c->tail).var !=
                    std::get<ContVar>(specific->tail).var) {
                    return false;
                }
            }
            else {
                std::vector<Kind> front;
                for (size_t i = min_size; i < specific->front.size(); ++i) {
                    front.push_back(specific->front[i]);
                }
                su.cont_map.insert_or_assign(
                    v, cont_kind(std::move(front), specific->tail));
            }
            return true;
        }
    }
}

namespace monad::vm::compiler::poly_typed
{
    Kind word = std::make_shared<PreKind>(Word{});

    Kind any = std::make_shared<PreKind>(Any{});

    Kind kind_var(VarName v)
    {
        return std::make_shared<PreKind>(KindVar{v});
    }

    Kind literal_var(VarName v, ContKind c)
    {
        return std::make_shared<PreKind>(LiteralVar{v, c});
    }

    Kind word_cont(ContKind c)
    {
        return std::make_shared<PreKind>(WordCont{c});
    }

    Kind cont(ContKind c)
    {
        return std::make_shared<PreKind>(Cont{c});
    }

    ContKind cont_words = cont_kind({});

    ContKind cont_kind(std::vector<Kind> kinds, ContTailKind t)
    {
        return std::make_shared<PreContKind>(std::move(kinds), t);
    }

    ContKind cont_kind(std::vector<Kind> kinds, VarName v)
    {
        return std::make_shared<PreContKind>(std::move(kinds), ContVar{v});
    }

    ContKind cont_kind(std::vector<Kind> kinds)
    {
        return std::make_shared<PreContKind>(std::move(kinds), ContWords{});
    }

    void format_cont(ContKind const &cont, std::format_context &ctx)
    {
        using monad::vm::Cases;

        for (auto const &k : cont->front) {
            format_kind(k, ctx, true);
            std::format_to(ctx.out(), ",");
        }
        std::visit(
            Cases{
                [&ctx](ContVar const &cv) {
                    std::format_to(ctx.out(), "s{} -> Exit", cv.var);
                },
                [&ctx](ContWords const &) {
                    std::format_to(ctx.out(), "Word.. -> Exit");
                }},
            cont->tail);
    }

    void
    format_kind(Kind const &kind, std::format_context &ctx, bool use_parens)
    {
        using monad::vm::Cases;

        std::visit(
            Cases{
                [&ctx](Word const &) { std::format_to(ctx.out(), "Word"); },
                [&ctx](Any const &) { std::format_to(ctx.out(), "Any"); },
                [&ctx](KindVar const &kv) {
                    std::format_to(ctx.out(), "v{}", kv.var);
                },
                [&ctx, use_parens](LiteralVar const &lv) {
                    if (use_parens) {
                        std::format_to(ctx.out(), "(");
                    }
                    std::format_to(ctx.out(), "L{} : ", lv.var);
                    format_cont(lv.cont, ctx);
                    if (use_parens) {
                        std::format_to(ctx.out(), ")");
                    }
                },
                [&ctx, use_parens](WordCont const &wc) {
                    if (use_parens) {
                        std::format_to(ctx.out(), "(");
                    }
                    std::format_to(ctx.out(), "Word : ");
                    format_cont(wc.cont, ctx);
                    if (use_parens) {
                        std::format_to(ctx.out(), ")");
                    }
                },
                [&ctx, use_parens](Cont const &c) {
                    if (use_parens) {
                        std::format_to(ctx.out(), "(");
                    }
                    format_cont(c.cont, ctx);
                    if (use_parens) {
                        std::format_to(ctx.out(), ")");
                    }
                }},
            *kind);
    }

    bool alpha_equal(Kind k1, Kind k2)
    {
        PolyVarSubstMap su1;
        PolyVarSubstMap su2;
        return kind_alpha_eq(su1, std::move(k1), su2, std::move(k2));
    }

    bool alpha_equal(ContKind c1, ContKind c2)
    {
        PolyVarSubstMap su1;
        PolyVarSubstMap su2;
        return cont_alpha_eq(su1, std::move(c1), su2, std::move(c2));
    }

    bool weak_equal(Kind k1, Kind k2)
    {
        using monad::vm::Cases;

        if (k1->index() != k2->index()) {
            return false;
        }
        return std::visit(
            Cases{
                [](Word const &) { return true; },
                [](Any const &) { return true; },
                [&k2](KindVar const &kv1) {
                    KindVar const &kv2 = std::get<KindVar>(*k2);
                    return kv1.var == kv2.var;
                },
                [&k2](LiteralVar const &lv1) {
                    LiteralVar const &lv2 = std::get<LiteralVar>(*k2);
                    if (lv1.var != lv2.var) {
                        return false;
                    }
                    return weak_equal(lv1.cont, lv2.cont);
                },
                [&k2](WordCont const &wc1) {
                    WordCont const &wc2 = std::get<WordCont>(*k2);
                    return weak_equal(wc1.cont, wc2.cont);
                },
                [&k2](Cont const &c1) {
                    Cont const &c2 = std::get<Cont>(*k2);
                    return weak_equal(c1.cont, c2.cont);
                }},
            *k1);
    }

    bool weak_equal(ContKind c1, ContKind c2)
    {
        using monad::vm::Cases;

        if (c1->tail.index() != c2->tail.index()) {
            return false;
        }
        if (c1->front.size() != c2->front.size() &&
            std::holds_alternative<ContVar>(c1->tail)) {
            return false;
        }
        size_t const min_size = std::min(c1->front.size(), c2->front.size());
        for (size_t i = 0; i < min_size; ++i) {
            if (!weak_equal(c1->front[i], c2->front[i])) {
                return false;
            }
        }
        for (size_t i = min_size; i < c1->front.size(); ++i) {
            if (!std::holds_alternative<Word>(*c1->front[i])) {
                return false;
            }
        }
        for (size_t i = min_size; i < c2->front.size(); ++i) {
            if (!std::holds_alternative<Word>(*c2->front[i])) {
                return false;
            }
        }
        return std::visit(
            Cases{
                [&c2](ContVar const &cv1) {
                    ContVar const &cv2 = std::get<ContVar>(c2->tail);
                    return cv1.var == cv2.var;
                },
                [](ContWords const &) { return true; }},
            c1->tail);
    }

    bool can_specialize(Kind generic, Kind specific)
    {
        SpecializeSubstMap su;
        return ::can_specialize(su, generic, specific);
    }

    bool can_specialize(ContKind generic, ContKind specific)
    {
        SpecializeSubstMap su;
        return ::can_specialize(su, generic, specific);
    }
}
