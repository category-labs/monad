#pragma once

#include <monad/core/address.hpp>
#include <monad/core/byte_string.hpp>
#include <monad/core/int.hpp>
#include <monad/evm/config.hpp>

MONAD_EVM_NAMESPACE_BEGIN

// YP Section 8
struct CallParameters
{
    Address sender; // s
    Address const &origin; // o
    Address recipient; // r
    Address code_address; // c
    uint64_t gas; // g
    uint256_t value; // v
    uint256_t const &gas_price; // p
    byte_string_view input_data; // d
    size_t depth; // e
    bool can_modify_state; // w
};

static_assert(sizeof(CallParameters) == 152);
static_assert(alignof(CallParameters) == 8);

MONAD_EVM_NAMESPACE_END
