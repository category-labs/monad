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

#include <category/execution/monad/graph_eval/config.hpp>
#include <category/execution/monad/graph_eval/ops.hpp>
#include <category/execution/monad/graph_eval/fuse_compiler.hpp>

MONAD_GRAPH_EVAL_ANONYMOUS_NAMESPACE_BEGIN

class FuseCompilerImpl
{
};

MONAD_GRAPH_EVAL_ANONYMOUS_NAMESPACE_END


MONAD_GRAPH_EVAL_NAMESPACE_BEGIN

Result<FuseCompiledGraph>
FuseCompiler::compile(std::span<uint8_t const> gc, State &state)
{
    MONAD_ABORT();
}

MONAD_GRAPH_EVAL_NAMESPACE_END
