#include <category/vm/compiler/ir/poly_typed/exceptions.hpp>
#include <category/vm/compiler/ir/poly_typed/kind.hpp>
#include <category/vm/compiler/ir/poly_typed/subst_map.hpp>
#include <category/vm/core/assert.h>
#include <category/vm/core/cases.hpp>

#include <algorithm>
#include <cstddef>
#include <exception>
#include <optional>
#include <unordered_set>
#include <utility>
#include <variant>
#include <vector>

namespace monad::vm::compiler::poly_typed
{
    void SubstMap::reset()
    {
        cont_map = {};
        kind_map = {};
    }

    std::optional<LiteralType> SubstMap::get_literal_type(VarName v)
    {
        auto it = literal_map.find(v);
        if (it == literal_map.end()) {
            return std::nullopt;
        }
        return it->second;
    }

    std::optional<Kind> SubstMap::get_kind(VarName v)
    {
        auto it = kind_map.find(v);
        if (it == kind_map.end()) {
            return std::nullopt;
        }
        return it->second;
    }

    std::optional<ContKind> SubstMap::get_cont(VarName v)
    {
        auto it = cont_map.find(v);
        if (it == cont_map.end()) {
            return std::nullopt;
        }
        return it->second;
    }

    void SubstMap::link_literal_vars(VarName v1, VarName v2)
    {
        MONAD_VM_DEBUG_ASSERT(
            !literal_map.contains(v1) && !literal_map.contains(v2));

        auto links1 = literal_links.find_or_default(v1);
        links1.insert(v2);
        literal_links.put(v1, std::move(links1));

        auto links2 = literal_links.find_or_default(v2);
        links2.insert(v1);
        literal_links.put(v2, std::move(links2));
    }

    void SubstMap::insert_literal_type(VarName v0, LiteralType t)
    {
        std::unordered_set<VarName> visited;
        std::vector<VarName> work_stack{v0};
        while (!work_stack.empty()) {
            VarName const v = work_stack.back();
            work_stack.pop_back();
            if (!visited.insert(v).second) {
                continue;
            }
            __attribute__((unused)) bool const ins = literal_map.put(v, t);
            MONAD_VM_DEBUG_ASSERT(ins || t == LiteralType::Word);
            auto lit = literal_links.find(v);
            if (lit != literal_links.end()) {
                for (auto w : lit->second) {
                    work_stack.push_back(w);
                }
            }
        }
    }

    ContKind SubstMap::subst(ContKind cont, size_t depth, size_t &ticks)
    {
        increment_kind_depth(depth, 1);
        increment_kind_ticks(ticks, cont->front.size());

        std::vector<Kind> kinds = cont->front;
        ContTailKind t = cont->tail;
        while (std::holds_alternative<ContVar>(t)) {
            auto new_c = cont_map.find(std::get<ContVar>(t).var);
            if (new_c == cont_map.end()) {
                break;
            }
            increment_kind_ticks(ticks, 1 + new_c->second->front.size());
            kinds.insert(
                kinds.end(),
                new_c->second->front.begin(),
                new_c->second->front.end());
            t = new_c->second->tail;
        }
        for (auto &kind : kinds) {
            kind = subst(kind, depth, ticks);
        }
        return cont_kind(std::move(kinds), t);
    }

    Kind SubstMap::subst(Kind kind, size_t depth, size_t &ticks)
    {
        using monad::vm::Cases;

        increment_kind_depth(depth, 1);

        while (std::holds_alternative<KindVar>(*kind)) {
            auto new_k = kind_map.find(std::get<KindVar>(*kind).var);
            if (new_k == kind_map.end()) {
                return kind;
            }
            increment_kind_ticks(ticks, 1);
            kind = new_k->second;
        }

        return std::visit(
            Cases{
                [](Word const &) { return word; },
                [](Any const &) { return any; },
                [](KindVar const &) -> Kind {
                    // unreachable
                    std::terminate();
                },
                [this, depth, &ticks](LiteralVar const &lv) {
                    auto t = literal_map.find(lv.var);
                    if (t == literal_map.end()) {
                        increment_kind_ticks(ticks, 1);
                        auto v = subst_literal_var_name(lv.var);
                        return literal_var(v, subst(lv.cont, depth, ticks));
                    }
                    switch (t->second) {
                    case LiteralType::Cont:
                        increment_kind_ticks(ticks, 1);
                        return cont(subst(lv.cont, depth, ticks));
                    case LiteralType::WordCont:
                        increment_kind_ticks(ticks, 1);
                        return word_cont(subst(lv.cont, depth, ticks));
                    case LiteralType::Word:
                        return word;
                    }
                    std::terminate();
                },
                [this, depth, &ticks](WordCont const &wc) {
                    increment_kind_ticks(ticks, 1);
                    return word_cont(subst(wc.cont, depth, ticks));
                },
                [this, depth, &ticks](Cont const &c) {
                    increment_kind_ticks(ticks, 1);
                    return cont(subst(c.cont, depth, ticks));
                }},
            *kind);
    }

    std::optional<ContKind> SubstMap::subst(ContKind c)
    {
        try {
            size_t ticks = 0;
            return subst(std::move(c), 0, ticks);
        }
        catch (InferException const &) {
            return std::nullopt;
        }
    }

    std::optional<Kind> SubstMap::subst(Kind k)
    {
        try {
            size_t ticks = 0;
            return subst(std::move(k), 0, ticks);
        }
        catch (InferException const &) {
            return std::nullopt;
        }
    }

    ContKind SubstMap::subst_or_throw(ContKind c)
    {
        size_t ticks = 0;
        return subst(std::move(c), 0, ticks);
    }

    Kind SubstMap::subst_or_throw(Kind k)
    {
        size_t ticks = 0;
        return subst(std::move(k), 0, ticks);
    }

    std::vector<VarName> SubstMap::subst_to_var(ContKind cont)
    {
        std::vector<VarName> ret;
        for (;;) {
            for (auto &k : cont->front) {
                ret.push_back(subst_to_var(k));
            }
            if (!std::holds_alternative<ContVar>(cont->tail)) {
                break;
            }
            auto new_c = cont_map.find(std::get<ContVar>(cont->tail).var);
            if (new_c == cont_map.end()) {
                break;
            }
            cont = new_c->second;
        }
        return ret;
    }

    VarName SubstMap::subst_to_var(Kind kind)
    {
        VarName ret = std::get<KindVar>(*kind).var;
        auto new_k = kind_map.find(ret);
        while (new_k != kind_map.end() &&
               std::holds_alternative<KindVar>(*new_k->second)) {
            ret = std::get<KindVar>(*new_k->second).var;
            new_k = kind_map.find(ret);
        }
        return ret;
    }

    void SubstMap::transaction()
    {
        literal_map.transaction();
        literal_links.transaction();
        cont_map.transaction();
        kind_map.transaction();
    }

    void SubstMap::commit()
    {
        literal_map.commit();
        literal_links.commit();
        cont_map.commit();
        kind_map.commit();
    }

    void SubstMap::revert()
    {
        literal_map.revert();
        literal_links.revert();
        cont_map.revert();
        kind_map.revert();
    }

    VarName SubstMap::subst_literal_var_name(VarName v0)
    {
        VarName min_var_name = v0;
        std::unordered_set<VarName> visited;
        std::vector<VarName> work_stack{v0};
        while (!work_stack.empty()) {
            VarName const v = work_stack.back();
            work_stack.pop_back();
            if (!visited.insert(v).second) {
                continue;
            }
            min_var_name = std::min(min_var_name, v);
            auto lit = literal_links.find(v);
            if (lit != literal_links.end()) {
                for (auto w : lit->second) {
                    work_stack.push_back(w);
                }
            }
        }
        return min_var_name;
    }
}
