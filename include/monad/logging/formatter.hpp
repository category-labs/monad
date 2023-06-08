#pragma once

#include <monad/execution/replay_block_db.hpp>

#include <quill/Quill.h>

#include <type_traits>

namespace quill
{
    template <>
    struct copy_loggable<monad::bytes32_t> : std::true_type
    {
    };

    template <>
    struct copy_loggable<uint64_t> : std::true_type
    {
    };

    template <typename T>
    struct copy_loggable<std::optional<T>>
        : std::integral_constant<bool, detail::is_registered_copyable_v<T>>
    {
    };
}

namespace fmt
{

    template <>
    struct formatter<monad::bytes32_t>
    {
        template <typename ParseContext>
        constexpr auto parse(ParseContext &ctx)
        {
            return ctx.begin();
        }

        template <typename FormatContext>
        auto format(const monad::bytes32_t &value, FormatContext &ctx)
        {
            for (const auto &byte : value.bytes) {
                fmt::format_to(ctx.out(), "{:02x}", byte);
            }
            return ctx.out();
        }
    };
}