#pragma once

#include <monad/rlp/config.hpp>

#include <exception>
#include <variant>

MONAD_RLP_NAMESPACE_BEGIN

enum class RLPDecodeError
{
    OVERFLOW,
    TYPE_UNEXPECTED,
    INPUT_TOO_SHORT,
    INPUT_TOO_LONG,
    ARRAY_LENGTH_UNEXPECTED,
    INVALID_TXN_TYPE,
    LEADING_ZERO,
};

// TODO: This enum will be populated later
enum class RLPEncodeError
{

};

class RLPException : public std::exception
{
    using RLPError = std::variant<RLPDecodeError, RLPEncodeError>;
    RLPError error_;

public:
    template <typename RLPError>
    explicit RLPException(RLPError const error)
        : error_(error)
    {
    }

    virtual char const *what() const noexcept override
    {
        if (std::holds_alternative<RLPDecodeError>(error_)) {
            auto const *decode_error = std::get_if<RLPDecodeError>(&error_);
            switch (*decode_error) {
            case RLPDecodeError::OVERFLOW:
                return "Decode: Value Overflow";
            case RLPDecodeError::TYPE_UNEXPECTED:
                return "Decode: String where list is expected (or vice versa)";
            case RLPDecodeError::INPUT_TOO_SHORT:
                return "Decode: Encoded string is too short";
            case RLPDecodeError::INPUT_TOO_LONG:
                return "Decode: Encoded string is too long";
            case RLPDecodeError::ARRAY_LENGTH_UNEXPECTED:
                return "Decode: Array size mismatch";
            case RLPDecodeError::INVALID_TXN_TYPE:
                return "Decode: Unsupported transaction type";
            case RLPDecodeError::LEADING_ZERO:
                return "Decode: Encoded string has leading zeros";
            default:
                return "Decode: Unexpected decoding error";
            }
        }
        else {
            MONAD_DEBUG_ASSERT(std::holds_alternative<RLPEncodeError>(error_));
            return "Encode: Unknown error (for now)";
        }
    }
};

MONAD_RLP_NAMESPACE_END
