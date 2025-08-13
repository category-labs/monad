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

#include <category/vm/compiler/ir/poly_typed/exceptions.hpp>
#include <category/vm/compiler/ir/poly_typed/kind.hpp>
#include <category/vm/compiler/ir/poly_typed/subst_map.hpp>
#include <category/vm/compiler/ir/poly_typed/unify.hpp>
#include <category/vm/core/assert.h>
#include <category/vm/core/cases.hpp>

#include <cstddef>
#include <cstdint>
#include <exception>
#include <optional>
#include <utility>
#include <variant>
#include <vector>

namespace
{
    using namespace monad::vm::compiler;
    using namespace monad::vm::compiler::poly_typed;

    ContKind find_subst_cont2(
        SubstMap &, VarName, bool is_kind_var, ContKind, size_t depth,
        size_t &ticks);

    Kind find_subst_kind2(
        SubstMap &su, VarName var, bool is_kind_var, Kind kind, size_t depth,
        size_t &ticks)
    {
        using monad::vm::Cases;

        increment_kind_depth(depth, 1);
        while (std::holds_alternative<KindVar>(*kind)) {
            auto new_k = su.get_kind(std::get<KindVar>(*kind).var);
            if (!new_k.has_value()) {
                break;
            }
            increment_kind_ticks(ticks, 1);
            kind = *new_k;
        }
        return std::visit(
            Cases{
                [](Word const &) { return word; },
                [](Any const &) { return any; },
                [var, is_kind_var, &kind](KindVar const &kv) {
                    if (is_kind_var && kv.var == var) {
                        throw UnificationException{};
                    }
                    return kind;
                },
                [&su, var, is_kind_var, depth, &ticks](LiteralVar const &lv) {
                    auto t = su.get_literal_type(lv.var);
                    if (!t.has_value()) {
                        increment_kind_ticks(ticks, 1);
                        su.transaction();
                        try {
                            ContKind const k = find_subst_cont2(
                                su, var, is_kind_var, lv.cont, depth, ticks);
                            su.commit();
                            return literal_var(lv.var, k);
                        }
                        catch (UnificationException const &) {
                            su.revert();
                            su.insert_literal_type(lv.var, LiteralType::Word);
                            return word;
                        }
                    }
                    switch (*t) {
                    case LiteralType::Cont:
                        increment_kind_ticks(ticks, 1);
                        return cont(find_subst_cont2(
                            su, var, is_kind_var, lv.cont, depth, ticks));
                    case LiteralType::WordCont:
                        increment_kind_ticks(ticks, 1);
                        return word_cont(find_subst_cont2(
                            su, var, is_kind_var, lv.cont, depth, ticks));
                    case LiteralType::Word:
                        return word;
                    }
                    std::terminate();
                },
                [&su, var, is_kind_var, depth, &ticks](WordCont const &wc) {
                    increment_kind_ticks(ticks, 1);
                    return word_cont(find_subst_cont2(
                        su, var, is_kind_var, wc.cont, depth, ticks));
                },
                [&su, var, is_kind_var, depth, &ticks](Cont const &c) {
                    increment_kind_ticks(ticks, 1);
                    return cont(find_subst_cont2(
                        su, var, is_kind_var, c.cont, depth, ticks));
                }},
            *kind);
    }

    ContKind find_subst_cont2(
        SubstMap &su, VarName var, bool is_kind_var, ContKind cont,
        size_t depth, size_t &ticks)
    {
        increment_kind_depth(depth, 1);
        increment_kind_ticks(ticks, cont->front.size());
        std::vector<Kind> kinds = cont->front;
        ContTailKind t = cont->tail;
        while (std::holds_alternative<ContVar>(t)) {
            ContVar const cv = std::get<ContVar>(t);
            auto copt = su.get_cont(cv.var);
            if (!copt.has_value()) {
                if (!is_kind_var && cv.var == var) {
                    throw UnificationException{};
                }
                break;
            }
            increment_kind_ticks(ticks, 1 + (*copt)->front.size());
            kinds.insert(
                kinds.end(), (*copt)->front.begin(), (*copt)->front.end());
            t = (*copt)->tail;
        }
        for (auto &kind : kinds) {
            kind = find_subst_kind2(su, var, is_kind_var, kind, depth, ticks);
        }
        return cont_kind(std::move(kinds), t);
    }

    std::optional<Kind> find_subst_kind(
        SubstMap &su, VarName var, Kind kind, size_t depth, size_t &ticks)
    {
        MONAD_VM_DEBUG_ASSERT(!su.get_kind(var).has_value());
        while (std::holds_alternative<KindVar>(*kind)) {
            auto new_k = su.get_kind(std::get<KindVar>(*kind).var);
            if (!new_k.has_value()) {
                if (std::get<KindVar>(*kind).var == var) {
                    return std::nullopt;
                }
                return kind;
            }
            increment_kind_ticks(ticks, 1);
            kind = *new_k;
        }
        return find_subst_kind2(su, var, true, kind, depth, ticks);
    }

    std::optional<ContKind> find_subst_cont(
        SubstMap &su, VarName var, ContKind cont, size_t depth, size_t &ticks)
    {
        MONAD_VM_DEBUG_ASSERT(!su.get_cont(var).has_value());
        while (std::holds_alternative<ContVar>(cont->tail) &&
               cont->front.empty()) {
            ContVar const cv = std::get<ContVar>(cont->tail);
            auto copt = su.get_cont(cv.var);
            if (!copt.has_value()) {
                if (cv.var == var) {
                    return std::nullopt;
                }
                return cont;
            }
            increment_kind_ticks(ticks, 1);
            cont = *copt;
        }
        return find_subst_cont2(su, var, false, cont, depth, ticks);
    }

    void
    unify(SubstMap &su, ContKind k1, ContKind k2, size_t depth, size_t &ticks);

    void unify_literal_var_to_type(
        SubstMap &su, LiteralVar const &lv1, LiteralVar const &lv2,
        LiteralType t2, size_t depth, size_t &ticks)
    {
        switch (t2) {
        case LiteralType::Word:
            su.insert_literal_type(lv1.var, LiteralType::Word);
            break;
        case LiteralType::Cont:
            su.insert_literal_type(lv1.var, LiteralType::Cont);
            increment_kind_ticks(ticks, 1);
            unify(su, lv1.cont, lv2.cont, depth, ticks);
            break;
        case LiteralType::WordCont:
            su.insert_literal_type(lv1.var, LiteralType::WordCont);
            increment_kind_ticks(ticks, 1);
            unify(su, lv1.cont, lv2.cont, depth, ticks);
            break;
        }
    }

    void unify_literal_vars(
        SubstMap &su, LiteralVar const &lv1, LiteralVar const &lv2,
        size_t depth, size_t &ticks)
    {
        auto t1 = su.get_literal_type(lv1.var);
        auto t2 = su.get_literal_type(lv2.var);
        if (!t1.has_value() && !t2.has_value()) {
            su.transaction();
            try {
                su.link_literal_vars(lv1.var, lv2.var);
                increment_kind_ticks(ticks, 1);
                unify(su, lv1.cont, lv2.cont, depth, ticks);
                su.commit();
            }
            catch (UnificationException const &) {
                su.revert();
                su.insert_literal_type(lv1.var, LiteralType::Word);
                su.insert_literal_type(lv2.var, LiteralType::Word);
            }
            return;
        }
        if (!t2.has_value()) {
            return unify_literal_var_to_type(su, lv2, lv1, *t1, depth, ticks);
        }
        if (!t1.has_value()) {
            return unify_literal_var_to_type(su, lv1, lv2, *t2, depth, ticks);
        }
        if (*t1 != *t2) {
            throw UnificationException{};
        }
        if (*t1 != LiteralType::Word) {
            unify(su, lv1.cont, lv2.cont, depth, ticks);
        }
    }

    void unify(SubstMap &su, Kind k1, Kind k2, size_t depth, size_t &ticks)
    {
        using monad::vm::Cases;

        increment_kind_depth(depth, 1);
        while (std::holds_alternative<KindVar>(*k1)) {
            auto new_k = su.get_kind(std::get<KindVar>(*k1).var);
            if (!new_k.has_value()) {
                break;
            }
            increment_kind_ticks(ticks, 1);
            k1 = *new_k;
        }
        while (std::holds_alternative<KindVar>(*k2)) {
            auto new_k = su.get_kind(std::get<KindVar>(*k2).var);
            if (!new_k.has_value()) {
                break;
            }
            increment_kind_ticks(ticks, 1);
            k2 = *new_k;
        }
        if (!std::holds_alternative<KindVar>(*k1)) {
            if (std::holds_alternative<KindVar>(*k2) ||
                std::holds_alternative<LiteralVar>(*k2)) {
                std::swap(k1, k2);
            }
        }
        std::visit(
            Cases{
                [&k2](Word const &) {
                    if (!std::holds_alternative<Word>(*k2)) {
                        throw UnificationException{};
                    }
                },
                [&k2](Any const &) {
                    if (!std::holds_alternative<Any>(*k2)) {
                        throw UnificationException{};
                    }
                },
                [&su, &k2, depth, &ticks](KindVar const &kv1) {
                    auto kopt2 = find_subst_kind(su, kv1.var, k2, depth, ticks);
                    if (kopt2.has_value()) {
                        su.insert_kind(kv1.var, *kopt2);
                    }
                },
                [&su, &k2, depth, &ticks](LiteralVar const &lv1) {
                    std::visit(
                        Cases{
                            [&su, &lv1](Word const &) {
                                auto t1 = su.get_literal_type(lv1.var);
                                if (t1.has_value()) {
                                    if (t1 != LiteralType::Word) {
                                        throw UnificationException{};
                                    }
                                }
                                else {
                                    su.insert_literal_type(
                                        lv1.var, LiteralType::Word);
                                }
                            },
                            [](Any const &) { throw UnificationException{}; },
                            [](KindVar const &) {
                                // unreachable
                                std::terminate();
                            },
                            [&su, &lv1, depth, &ticks](LiteralVar const &lv2) {
                                unify_literal_vars(su, lv1, lv2, depth, ticks);
                            },
                            [&su, &lv1, depth, &ticks](WordCont const &wc2) {
                                increment_kind_ticks(ticks, 1);
                                auto t1 = su.get_literal_type(lv1.var);
                                if (t1.has_value()) {
                                    if (t1 != LiteralType::WordCont) {
                                        throw UnificationException{};
                                    }
                                    unify(su, lv1.cont, wc2.cont, depth, ticks);
                                }
                                else {
                                    su.insert_literal_type(
                                        lv1.var, LiteralType::WordCont);
                                    unify(su, lv1.cont, wc2.cont, depth, ticks);
                                }
                            },
                            [&su, &lv1, depth, &ticks](Cont const &c2) {
                                increment_kind_ticks(ticks, 1);
                                auto t1 = su.get_literal_type(lv1.var);
                                if (t1.has_value()) {
                                    if (t1 != LiteralType::Cont) {
                                        throw UnificationException{};
                                    }
                                    unify(su, lv1.cont, c2.cont, depth, ticks);
                                }
                                else {
                                    su.insert_literal_type(
                                        lv1.var, LiteralType::Cont);
                                    unify(su, lv1.cont, c2.cont, depth, ticks);
                                }
                            }},
                        *k2);
                },
                [&su, &k2, depth, &ticks](WordCont const &wc1) {
                    if (!std::holds_alternative<WordCont>(*k2)) {
                        throw UnificationException{};
                    }
                    WordCont const &wc2 = std::get<WordCont>(*k2);
                    increment_kind_ticks(ticks, 1);
                    unify(su, wc1.cont, wc2.cont, depth, ticks);
                },
                [&su, &k2, depth, &ticks](Cont const &c1) {
                    if (!std::holds_alternative<Cont>(*k2)) {
                        throw UnificationException{};
                    }
                    Cont const &c2 = std::get<Cont>(*k2);
                    increment_kind_ticks(ticks, 1);
                    unify(su, c1.cont, c2.cont, depth, ticks);
                }},
            *k1);
    }

    void
    unify(SubstMap &su, ContKind c1, ContKind c2, size_t depth, size_t &ticks)
    {
        using monad::vm::Cases;

        increment_kind_depth(depth, 1);

        increment_kind_ticks(ticks, c2->front.size() + c1->front.size());
        size_t index1 = 0;
        size_t index2 = 0;
        for (;;) {
            if (index1 == c1->front.size()) {
                if (std::holds_alternative<ContVar>(c1->tail)) {
                    auto c = su.get_cont(std::get<ContVar>(c1->tail).var);
                    if (!c.has_value()) {
                        break;
                    }
                    index1 = 0;
                    c1 = *c;
                    increment_kind_ticks(ticks, 1 + c1->front.size());
                    continue;
                }
                else {
                    break;
                }
            }
            if (index2 == c2->front.size()) {
                if (std::holds_alternative<ContVar>(c2->tail)) {
                    auto c = su.get_cont(std::get<ContVar>(c2->tail).var);
                    if (!c.has_value()) {
                        break;
                    }
                    index2 = 0;
                    c2 = *c;
                    increment_kind_ticks(ticks, 1 + c2->front.size());
                    continue;
                }
                else {
                    break;
                }
            }
            unify(su, c1->front[index1], c2->front[index2], depth, ticks);
            ++index1;
            ++index2;
        }

        if (c1->front.size() > index1) {
            std::swap(c1, c2);
            index2 = index1;
        }

        std::visit(
            Cases{
                [&su, &c2, depth, &ticks, &index2](ContVar const &cv1) {
                    std::vector<Kind> n;
                    for (; index2 < c2->front.size(); ++index2) {
                        n.push_back(c2->front[index2]);
                    }
                    auto kopt = find_subst_cont(
                        su, cv1.var, cont_kind(n, c2->tail), depth, ticks);
                    if (kopt.has_value()) {
                        su.insert_cont(cv1.var, *kopt);
                    }
                },
                [&su, &c2, depth, &ticks, &index2](ContWords const &) {
                    for (;;) {
                        for (; index2 < c2->front.size(); ++index2) {
                            unify(su, word, c2->front[index2], depth, ticks);
                        }
                        if (!std::holds_alternative<ContVar>(c2->tail)) {
                            break;
                        }
                        auto c = su.get_cont(std::get<ContVar>(c2->tail).var);
                        if (!c.has_value()) {
                            break;
                        }
                        index2 = 0;
                        c2 = *c;
                        increment_kind_ticks(ticks, 1 + c2->front.size());
                    }
                    if (std::holds_alternative<ContVar>(c2->tail)) {
                        su.insert_cont(
                            std::get<ContVar>(c2->tail).var, cont_words);
                    }
                }},
            c1->tail);
    }

    void unify_param_var(
        SubstMap &su, VarName param_var, VarName new_param_var, size_t &ticks)
    {
        using monad::vm::Cases;

        Kind const param = kind_var(param_var);
        Kind const new_param = kind_var(new_param_var);
        VarName v = su.subst_to_var(param);
        VarName const new_v = su.subst_to_var(new_param);

        if (v == new_v) {
            return;
        }

        Kind k = su.subst(param, 0, ticks);
        Kind new_k = su.subst(new_param, 0, ticks);

        // Check that `v` and `new_v` does not appear in `new_k` and `k`,
        // respectively:
        static_cast<void>(find_subst_kind2(su, v, true, new_k, 0, ticks));
        static_cast<void>(find_subst_kind2(su, new_v, true, k, 0, ticks));

        std::visit(
            Cases{
                [&](__attribute__((unused)) KindVar const &kv1) {
                    MONAD_VM_DEBUG_ASSERT(v == kv1.var);
                    su.insert_kind(v, new_k);
                },
                [&](Word const &) {
                    std::visit(
                        Cases{
                            [&](Cont const &c2) {
                                su.insert_kind(param_var, word_cont(c2.cont));
                            },
                            [&](WordCont const &) {
                                su.insert_kind(param_var, new_k);
                            },
                            [&](auto const &) {
                                unify(su, k, new_k, 0, ticks);
                            },
                        },
                        *new_k);
                },
                [&](Cont const &c1) {
                    std::visit(
                        Cases{
                            [&](Word const &) {
                                su.insert_kind(param_var, word_cont(c1.cont));
                            },
                            [&](WordCont const &wc2) {
                                unify(su, c1.cont, wc2.cont, 0, ticks);
                                su.insert_kind(param_var, word_cont(c1.cont));
                            },
                            [&](auto const &) {
                                unify(su, k, new_k, 0, ticks);
                            },
                        },
                        *new_k);
                },
                [&](WordCont const &wc1) {
                    std::visit(
                        Cases{
                            [&](Word const &) {
                                // nop
                            },
                            [&](Cont const &c2) {
                                unify(su, wc1.cont, c2.cont, 0, ticks);
                            },
                            [&](auto const &) {
                                unify(su, k, new_k, 0, ticks);
                            },
                        },
                        *new_k);
                },
                [&](auto const &) { unify(su, k, new_k, 0, ticks); },
            },
            *k);
    }

    void unify_param_var_name_map(
        SubstMap &su, std::vector<VarName> const &param_vars,
        ParamVarNameMap const &param_map, size_t &ticks)
    {
        for (uint64_t stack_index = 0; stack_index < param_vars.size();
             ++stack_index) {
            auto param_it = param_map.find(stack_index);
            if (param_it == param_map.end()) {
                continue;
            }
            std::vector<VarName> const &new_param_vars = param_it->second;
            MONAD_VM_DEBUG_ASSERT(!new_param_vars.empty());
            increment_kind_ticks(ticks, new_param_vars.size());
            for (VarName const n : new_param_vars) {
                unify_param_var(su, param_vars[stack_index], n, ticks);
            }
        }
    }
}

namespace monad::vm::compiler::poly_typed
{
    void unify(SubstMap &su, Kind k1, Kind k2)
    {
        try {
            su.transaction();
            size_t ticks = 0;
            ::unify(su, k1, k2, 0, ticks);
            su.commit();
        }
        catch (InferException const &) {
            su.revert();
            throw;
        }
    }

    void unify(SubstMap &su, ContKind c1, ContKind c2)
    {
        try {
            su.transaction();
            size_t ticks = 0;
            ::unify(su, c1, c2, 0, ticks);
            su.commit();
        }
        catch (InferException const &) {
            su.revert();
            throw;
        }
    }

    void unify_param_var_name_map(
        SubstMap &su, std::vector<VarName> const &param_vars,
        ParamVarNameMap const &param_map)
    {
        try {
            su.transaction();
            size_t ticks = 0;
            ::unify_param_var_name_map(su, param_vars, param_map, ticks);
            su.commit();
        }
        catch (InferException const &) {
            su.revert();
            throw;
        }
    }
}
