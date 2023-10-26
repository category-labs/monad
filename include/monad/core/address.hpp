#pragma once

#include <monad/config.hpp>

#include <monad/core/basic_formatter.hpp>

#include <evmc/evmc.hpp>

MONAD_NAMESPACE_BEGIN

using address_t = ::evmc::address;

static_assert(sizeof(address_t) == 20);
static_assert(alignof(address_t) == 1);

MONAD_NAMESPACE_END

template <>
struct quill::copy_loggable<monad::address_t> : std::true_type
{
};

template <>
struct fmt::formatter<monad::address_t> : public monad::basic_formatter
{
    template <typename FormatContext>
    auto format(monad::address_t const &value, FormatContext &ctx) const
    {
        fmt::format_to(
            ctx.out(),
            "0x{:02x}",
            fmt::join(std::as_bytes(std::span(value.bytes)), ""));
        return ctx.out();
    }
};
