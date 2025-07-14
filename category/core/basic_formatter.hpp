#pragma once

#include <category/core/config.hpp>

#include <quill/Fmt.h>

namespace fmt = fmtquill::v10;

MONAD_NAMESPACE_BEGIN

struct BasicFormatter
{
    template <typename ParseContext>
    constexpr auto parse(ParseContext &ctx)
    {
        return ctx.begin();
    }
};

MONAD_NAMESPACE_END
