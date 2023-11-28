#pragma once

#include <monad/config.hpp>

MONAD_NAMESPACE_BEGIN

enum class ValidationStatus
{
    SUCCESS,

    // Block Validation Error
    WRONG_LOGS_BLOOM, // TODO used in execute
    INVALID_GAS_USED, // TODO used in execute
    BLOCK_ERROR, // TODO temporary translation

    // Transaction Validation Error
    INSUFFICIENT_BALANCE,
    INTRINSIC_GAS_GREATER_THAN_LIMIT,
    BAD_NONCE,
    SENDER_NOT_EOA,
    TYPE_NOT_SUPPORTED,
    MAX_FEE_LESS_THAN_BASE,
    PRIORITY_FEE_GREATER_THAN_MAX,
    NONCE_EXCEEDS_MAX,
    INIT_CODE_LIMIT_EXCEEDED,
    GAS_LIMIT_REACHED,
    WRONG_CHAIN_ID,
    MISSING_SENDER,
    GAS_LIMIT_OVERFLOW,
};

MONAD_NAMESPACE_END
