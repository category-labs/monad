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

#include <category/vm/compiler/ir/poly_typed/strongly_connected_components.hpp>
#include <category/vm/compiler/ir/poly_typed/subst_map.hpp>

namespace monad::vm::compiler::poly_typed
{
    void unify(SubstMap &, Kind, Kind);

    void unify(SubstMap &, ContKind, ContKind);

    using ParamVarNameMap = std::unordered_map<uint64_t, std::vector<VarName>>;

    void unify_param_var_name_map(
        SubstMap &, std::vector<VarName> const &, ParamVarNameMap const &);
}
