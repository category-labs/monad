#pragma once

#include <monad/config.hpp>

#include <monad/core/basic_formatter.hpp>

#include <evmc/evmc.hpp>

MONAD_NAMESPACE_BEGIN

using bytes32_t = ::evmc::bytes32;

static_assert(sizeof(bytes32_t) == 32);
static_assert(alignof(bytes32_t) == 1);

using namespace evmc::literals;
inline constexpr bytes32_t NULL_HASH{
    0xc5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470_bytes32};

inline constexpr bytes32_t NULL_LIST_HASH{
    0x1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347_bytes32};

// Root hash of an empty trie
inline constexpr bytes32_t NULL_ROOT{
    0x56e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421_bytes32};

MONAD_NAMESPACE_END

template <>
struct quill::copy_loggable<monad::bytes32_t> : std::true_type
{
};

template <>
struct fmt::formatter<monad::bytes32_t> : public monad::basic_formatter
{
    template <typename FormatContext>
    auto format(monad::bytes32_t const &value, FormatContext &ctx) const
    {
        fmt::format_to(
            ctx.out(),
            "0x{:02x}",
            fmt::join(std::as_bytes(std::span(value.bytes)), ""));
        return ctx.out();
    }
};
