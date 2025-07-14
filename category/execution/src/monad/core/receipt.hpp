#pragma once

#include <category/core/config.hpp>
#include <monad/core/address.hpp>
#include <category/core/byte_string.hpp>
#include <category/core/bytes.hpp>
#include <monad/core/transaction.hpp>

MONAD_NAMESPACE_BEGIN

struct Receipt
{
    using Bloom = byte_string_fixed<256>;

    struct Log
    {
        byte_string data{};
        std::vector<bytes32_t> topics{};
        Address address{};

        friend bool operator==(Log const &, Log const &) = default;
    };

    Bloom bloom{}; // R_b
    uint64_t status{}; // R_z
    uint64_t gas_used{}; // R_u
    TransactionType type{}; // R_x
    std::vector<Log> logs{}; // R_l

    void add_log(Receipt::Log const &);

    friend bool operator==(Receipt const &, Receipt const &) = default;
};

void populate_bloom(Receipt::Bloom &, Receipt::Log const &);

static_assert(sizeof(Receipt::Log) == 80);
static_assert(alignof(Receipt::Log) == 8);

static_assert(sizeof(Receipt) == 304);
static_assert(alignof(Receipt) == 8);

MONAD_NAMESPACE_END
