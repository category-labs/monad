// Copyright (C) 2026 Category Labs, Inc.
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

#include <category/core/address.hpp>
#include <category/execution/ethereum/chain/chain.hpp>
#include <category/execution/ethereum/state3/state.hpp>
#include <category/execution/ethereum/trace/call_tracer.hpp>
#include <category/execution/ethereum/trace/state_tracer.hpp>
#include <category/execution/monad/graph_eval/config.hpp>
#include <category/vm/evm/monad/revision.h>
#include <category/vm/evm/traits.hpp>

MONAD_GRAPH_EVAL_NAMESPACE_BEGIN

inline constexpr Address GRAPH_EVAL_CA = Address{0x1002};

class GraphEvalContract
{
    State &state_;
    CallTracerBase &call_tracer_;

public:
    GraphEvalContract(State &state, CallTracerBase &tracer);

    using PrecompileFunc = Result<byte_string> (GraphEvalContract::*)(
        byte_string_view, Address const &, uint256_be_t const &);

    template <Traits traits>
    static std::pair<PrecompileFunc, uint64_t>
    precompile_dispatch(byte_string_view &);

    template <Traits traits>
    Result<byte_string>
    precompile_eval_op(byte_string_view, Address const &, uint256_be_t const &);

    template <Traits traits>
    Result<byte_string>
    precompile_eval_graph(byte_string_view, Address const &, uint256_be_t const &);

    Result<byte_string> precompile_fallback(
        byte_string_view, Address const &, uint256_be_t const &);
};

MONAD_GRAPH_EVAL_NAMESPACE_END
