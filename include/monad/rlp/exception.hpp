#pragma once

#include <monad/rlp/config.hpp>

#include <exception>
#include <variant>

MONAD_RLP_NAMESPACE_BEGIN

enum class RLPDecodeError
{
    OVERFLOW,
    TYPE_UNEXPECTED,
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
