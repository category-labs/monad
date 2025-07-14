#pragma once

#include <monad/core/basic_formatter.hpp>
#include <monad/core/fmt/account_fmt.hpp>
#include <monad/core/fmt/address_fmt.hpp>
#include <monad/core/fmt/bytes_fmt.hpp>

#include <monad/state2/state_deltas.hpp>

template <typename T>
struct quill::copy_loggable<monad::Delta<T>>
    : std::integral_constant<bool, detail::is_registered_copyable_v<T>>
{
};

template <>
struct quill::copy_loggable<monad::StateDelta> : std::true_type
{
};

template <>
struct quill::copy_loggable<monad::StateDeltas> : std::true_type
{
};

template <>
struct quill::copy_loggable<monad::Code> : std::true_type
{
};

template <>
struct fmt::formatter<monad::StateDelta> : public monad::BasicFormatter
{
    template <typename FormatContext>
    auto format(monad::StateDelta const &state_delta, FormatContext &ctx) const
    {
        fmt::format_to(ctx.out(), "{{");
        fmt::format_to(ctx.out(), "Account Delta: {} ", state_delta.account);
        fmt::format_to(ctx.out(), "Storage Deltas: {{");
        for (auto const &[key, storage_delta] : state_delta.storage) {
            fmt::format_to(
                ctx.out(), " Key: {}, Storage Delta: {}", key, storage_delta);
        }
        fmt::format_to(ctx.out(), "}}");
        fmt::format_to(ctx.out(), "}}");

        return ctx.out();
    }
};

template <>
struct fmt::formatter<monad::StateDeltas> : public monad::BasicFormatter
{
    template <typename FormatContext>
    auto
    format(monad::StateDeltas const &state_deltas, FormatContext &ctx) const
    {
        fmt::format_to(ctx.out(), "{{");

        for (auto const &[address, state_delta] : state_deltas) {
            fmt::format_to(
                ctx.out(),
                " Address: {}, State Delta: {}",
                address,
                state_delta);
        }
        fmt::format_to(ctx.out(), "}}");

        return ctx.out();
    }
};

template <>
struct fmt::formatter<monad::Code> : public monad::BasicFormatter
{
    template <typename FormatContext>
    auto format(monad::Code const &code, FormatContext &ctx) const
    {
        fmt::format_to(ctx.out(), "{{");

        for (auto const &[code_hash, icode] : code) {
            MONAD_ASSERT(icode);
            fmt::format_to(
                ctx.out(),
                "Code Hash: {}, Code Value: 0x{:02x} ",
                code_hash,
                fmt::join(
                    std::as_bytes(std::span{icode->code(), icode->code_size()}),
                    ""));
        }
        fmt::format_to(ctx.out(), "}}");

        return ctx.out();
    }
};
