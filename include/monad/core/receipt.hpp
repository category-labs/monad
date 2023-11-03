#pragma once

#include <monad/config.hpp>
#include <monad/core/address.hpp>
#include <monad/core/byte_string.hpp>
#include <monad/core/bytes.hpp>
#include <monad/core/transaction.hpp>

MONAD_NAMESPACE_BEGIN

struct Receipt
{
    enum Status
    {
        FAILED,
        SUCCESS,
    };

    using Bloom = byte_string_fixed<256>;

    struct Log
    {
        byte_string data{};
        std::vector<bytes32_t> topics{};
        address_t address{};

        friend bool operator==(Log const &, Log const &) = default;
    };

    Bloom bloom{};
    uint64_t status{};
    uint64_t gas_used{};
    TransactionType type{};
    std::vector<Log> logs{};

    void add_log(Receipt::Log const &);
};

void populate_bloom(Receipt::Bloom &, Receipt::Log const &);

static_assert(sizeof(Receipt::Log) == 80);
static_assert(alignof(Receipt::Log) == 8);

static_assert(sizeof(Receipt) == 304);
static_assert(alignof(Receipt) == 8);

MONAD_NAMESPACE_END

template <>
struct quill::copy_loggable<monad::Receipt::Log> : std::true_type
{
};

template <>
struct quill::copy_loggable<monad::Receipt> : std::true_type
{
};

template <>
struct fmt::formatter<monad::Receipt::Log> : public monad::basic_formatter
{
    template <typename FormatContext>
    auto format(monad::Receipt::Log const &l, FormatContext &ctx) const
    {
        fmt::format_to(
            ctx.out(),
            "Log{{"
            "Data=0x{:02x} "
            "Topics={} "
            "Address={}"
            "}}",
            fmt::join(std::as_bytes(std::span(l.data)), ""),
            l.topics,
            l.address);
        return ctx.out();
    }
};

template <>
struct fmt::formatter<monad::Receipt> : public monad::basic_formatter
{
    template <typename FormatContext>
    auto format(monad::Receipt const &r, FormatContext &ctx) const
    {
        fmt::format_to(
            ctx.out(),
            "Receipt{{"
            "Bloom=0x{:02x} "
            "Status={} "
            "Gas Used={} "
            "Transaction Type={} "
            "Logs={}"
            "}}",
            fmt::join(std::as_bytes(std::span(r.bloom)), ""),
            r.status,
            r.gas_used,
            r.type,
            r.logs);
        return ctx.out();
    }
};
