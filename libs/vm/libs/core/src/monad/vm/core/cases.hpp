#pragma once

namespace monad::vm
{
    template <class... Ts>
    struct Cases : Ts...
    {
        using Ts::operator()...;
    };
}
