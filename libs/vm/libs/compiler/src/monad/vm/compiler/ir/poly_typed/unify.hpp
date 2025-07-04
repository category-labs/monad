#pragma once

#include <monad/vm/compiler/ir/poly_typed/strongly_connected_components.hpp>
#include <monad/vm/compiler/ir/poly_typed/subst_map.hpp>

namespace monad::vm::compiler::poly_typed
{
    void unify(SubstMap &, Kind, Kind);

    void unify(SubstMap &, ContKind, ContKind);

    using ParamVarNameMap = std::unordered_map<uint64_t, std::vector<VarName>>;

    void unify_param_var_name_map(
        SubstMap &, std::vector<VarName> const &, ParamVarNameMap const &);
}
