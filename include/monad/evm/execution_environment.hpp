#pragma once

#include <monad/core/address.hpp>
#include <monad/core/block.hpp>
#include <monad/core/byte_string.hpp>
#include <monad/evm/config.hpp>

MONAD_EVM_NAMESPACE_BEGIN

// 9.3
struct ExecutionEnvironment
{
    Address address; // I_a
    Address const &origin; // I_o
    uint256_t const &gas_price; // I_p
    byte_string_view input_data; // I_d
    Address sender; // I_s
    uint256_t value; // I_v
    byte_string code; // I_b TODO: make reference
    BlockHeader const &header; // I_H
    size_t depth; // I_e
    bool can_modify_state; // I_w
};

static_assert(sizeof(ExecutionEnvironment) == 168);
static_assert(alignof(ExecutionEnvironment) == 8);

MONAD_EVM_NAMESPACE_END
