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

    void add_log(Receipt::Log const &l);
};

void populate_bloom(Receipt::Bloom &b, Receipt::Log const &l);

static_assert(sizeof(Receipt::Log) == 80);
static_assert(alignof(Receipt::Log) == 8);

static_assert(sizeof(Receipt) == 304);
static_assert(alignof(Receipt) == 8);

MONAD_NAMESPACE_END
