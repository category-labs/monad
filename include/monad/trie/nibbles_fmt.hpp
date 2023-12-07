#pragma once

#include <monad/core/basic_formatter.hpp>
#include <monad/trie/nibbles.hpp>

template <>
struct quill::copy_loggable<monad::trie::Nibbles> : std::true_type
{
};

template <>
struct fmt::formatter<monad::trie::Nibbles> : public monad::BasicFormatter
{
    template <typename FormatContext>
    auto format(monad::trie::Nibbles const &n, FormatContext &ctx) const
    {
        fmt::format_to(ctx.out(), "0x");
        for (uint8_t i = 0; i < n.size(); ++i) {
            MONAD_DEBUG_ASSERT(n[i] <= 0xf);
            fmt::format_to(ctx.out(), "{:01x}", n[i]);
        }
        return ctx.out();
    }
};
