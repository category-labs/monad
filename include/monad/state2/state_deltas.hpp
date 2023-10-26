#pragma once

#include <monad/config.hpp>

#include <monad/core/account.hpp>
#include <monad/core/address.hpp>
#include <monad/core/basic_formatter.hpp>
#include <monad/core/byte_string.hpp>
#include <monad/core/bytes.hpp>

#include <ankerl/unordered_dense.h>

#include <optional>
#include <utility>

MONAD_NAMESPACE_BEGIN

template <class T>
using delta_t = std::pair<T const, T>;

using AccountDelta = delta_t<std::optional<Account>>;

static_assert(sizeof(AccountDelta) == 176);
static_assert(alignof(AccountDelta) == 8);

using StorageDelta = delta_t<bytes32_t>;

static_assert(sizeof(StorageDelta) == 64);
static_assert(alignof(StorageDelta) == 1);

struct StateDelta
{
    AccountDelta account;
    ankerl::unordered_dense::segmented_map<bytes32_t, StorageDelta> storage;
};

static_assert(sizeof(StateDelta) == 240);
static_assert(alignof(StateDelta) == 8);

using StateDeltas =
    ankerl::unordered_dense::segmented_map<address_t, StateDelta>;

static_assert(sizeof(StateDeltas) == 64);
static_assert(alignof(StateDeltas) == 8);

using Code = ankerl::unordered_dense::segmented_map<bytes32_t, byte_string>;

static_assert(sizeof(Code) == 64);
static_assert(alignof(Code) == 8);

bool can_merge(StateDeltas const &to, StateDeltas const &from);
void merge(StateDeltas &to, StateDeltas const &from);

void merge(Code &to, Code &from);

MONAD_NAMESPACE_END

template <typename T>
struct quill::copy_loggable<monad::delta_t<T>>
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
struct fmt::formatter<monad::StateDelta> : public monad::basic_formatter
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
struct fmt::formatter<monad::StateDeltas> : public monad::basic_formatter
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
struct fmt::formatter<monad::Code> : public monad::basic_formatter
{
    template <typename FormatContext>
    auto format(monad::Code const &code, FormatContext &ctx) const
    {
        fmt::format_to(ctx.out(), "{{");

        for (auto const &[code_hash, code_value] : code) {
            fmt::format_to(
                ctx.out(),
                "Code Hash: {}, Code Value: 0x{:02x} ",
                code_hash,
                fmt::join(std::as_bytes(std::span{code_value}), ""));
        }
        fmt::format_to(ctx.out(), "}}");

        return ctx.out();
    }
};
