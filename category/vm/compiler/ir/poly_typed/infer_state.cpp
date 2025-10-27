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

#include <category/vm/compiler/ir/basic_blocks.hpp>
#include <category/vm/compiler/ir/local_stacks.hpp>
#include <category/vm/compiler/ir/poly_typed/block.hpp>
#include <category/vm/compiler/ir/poly_typed/infer_state.hpp>
#include <category/vm/compiler/ir/poly_typed/kind.hpp>
#include <category/vm/compiler/types.hpp>
#include <category/vm/core/assert.h>
#include <category/vm/core/cases.hpp>

#include <cstdint>
#include <iterator>
#include <limits>
#include <optional>
#include <unordered_map>
#include <utility>
#include <variant>
#include <vector>

namespace
{
    using namespace monad::vm::compiler;
    using namespace monad::vm::compiler::poly_typed;

    void push_static_jumpdest(
        std::vector<block_id> &dest, InferState const &state,
        Value const &value)
    {
        auto d = state.get_jumpdest(value);
        if (d.has_value()) {
            dest.push_back(*d);
        }
    }

    template <std::input_iterator It>
        requires(std::is_same_v<
                 typename std::iterator_traits<It>::value_type, Value>)
    void push_static_jumpdests(
        std::vector<block_id> &dest, InferState const &state, It tail_begin,
        It tail_end)
    {
        for (auto it = tail_begin; it != tail_end; ++it) {
            push_static_jumpdest(dest, state, *it);
        }
    }

    Kind refresh(InferState &state, PolyVarSubstMap &su, Kind cont);

    ContKind refresh(InferState &state, PolyVarSubstMap &su, ContKind cont)
    {
        using monad::vm::Cases;

        std::vector<Kind> kinds;
        for (auto const &k : cont->front) {
            kinds.push_back(refresh(state, su, k));
        }
        return std::visit(
            Cases{
                [&state, &su, &kinds](ContVar const &cv) {
                    VarName new_v;
                    auto const it = su.cont_map.find(cv.var);
                    if (it != su.cont_map.end()) {
                        new_v = it->second;
                    }
                    else {
                        new_v = state.fresh_cont_var();
                        su.cont_map.insert_or_assign(cv.var, new_v);
                    }
                    return cont_kind(std::move(kinds), new_v);
                },
                [&kinds](ContWords const &) {
                    return cont_kind(std::move(kinds));
                },
            },
            cont->tail);
    }

    Kind refresh(InferState &state, PolyVarSubstMap &su, Kind kind)
    {
        using monad::vm::Cases;

        return std::visit(
            Cases{
                [](Word const &) { return word; },
                [](Any const &) { return any; },
                [&state, &su](KindVar const &kv) {
                    VarName new_v;
                    auto const it = su.kind_map.find(kv.var);
                    if (it != su.kind_map.end()) {
                        new_v = it->second;
                    }
                    else {
                        new_v = state.fresh_kind_var();
                        su.kind_map.insert_or_assign(kv.var, new_v);
                    }
                    return kind_var(new_v);
                },
                [&state, &su](LiteralVar const &lv) {
                    return literal_var(lv.var, refresh(state, su, lv.cont));
                },
                [&state, &su](WordCont const &wc) {
                    return word_cont(refresh(state, su, wc.cont));
                },
                [&state, &su](Cont const &c) {
                    return cont(refresh(state, su, c.cont));
                }},
            *kind);
    }
}

namespace monad::vm::compiler::poly_typed
{
    InferState::InferState(
        std::unordered_map<byte_offset, block_id> const &j,
        std::vector<local_stacks::Block> &&b)
        : jumpdests{j}
        , pre_blocks{std::move(b)}
        , next_cont_var_name{}
        , next_kind_var_name{}
        , next_literal_var_name{}
    {
    }

    void InferState::reset()
    {
        subst_map.reset();
        next_cont_var_name = 0;
        next_kind_var_name = 0;
    }

    ContKind InferState::get_type(block_id bid)
    {
        auto const it = block_types.find(bid);
        MONAD_VM_DEBUG_ASSERT(it != block_types.end());
        PolyVarSubstMap su;
        return refresh(*this, su, it->second);
    }

    std::optional<block_id> InferState::get_jumpdest(Value const &value) const
    {
        if (value.is != ValueIs::LITERAL) {
            return std::nullopt;
        }
        if (value.literal >
            uint256_t{std::numeric_limits<byte_offset>::max()}) {
            return std::nullopt;
        }

        static_assert(sizeof(byte_offset) <= sizeof(uint64_t));

        byte_offset const offset = static_cast<byte_offset>(value.literal[0]);

        auto const it = jumpdests.find(offset);
        if (it == jumpdests.end()) {
            return std::nullopt;
        }
        return it->second;
    }

    std::vector<block_id> InferState::static_successors(block_id b) const
    {
        std::vector<block_id> ret;
        auto const &block = pre_blocks[b];
        switch (block.terminator) {
        case basic_blocks::Terminator::FallThrough:
            ret.push_back(block.fallthrough_dest);
            push_static_jumpdests(
                ret, *this, block.output.begin(), block.output.end());
            break;
        case basic_blocks::Terminator::JumpI:
            MONAD_VM_DEBUG_ASSERT(block.output.size() >= 2);
            ret.push_back(block.fallthrough_dest);
            push_static_jumpdest(ret, *this, block.output[0]);
            push_static_jumpdests(
                ret, *this, block.output.begin() + 2, block.output.end());
            break;
        case basic_blocks::Terminator::Jump:
            MONAD_VM_DEBUG_ASSERT(block.output.size() >= 1);
            push_static_jumpdests(
                ret, *this, block.output.begin(), block.output.end());
            break;
        default:
            break;
        }
        return ret;
    }
}
