#pragma once

#include <type_traits>

namespace monad::vm::utils
{
    template <typename X, typename... Xs, typename Y, typename... Ys>
    consteval bool same_signature(X (*)(Xs...), Y (*)(Ys...)) noexcept
    {
        return std::is_same_v<X, Y> && (std::is_same_v<Xs, Ys> && ...);
    }
}
