#pragma once

#include <monad/core/byte_string.hpp>
#include <monad/core/result.hpp>
#include <monad/rlp/config.hpp>

#include <boost/outcome/experimental/status-code/quick_status_code_from_enum.hpp>

MONAD_RLP_NAMESPACE_BEGIN

enum class DecodeError
{
    SUCCESS = 0,
    OVERFLOW,
    UNEXPECTED_LIST,
    UNEXPECTED_LENGTH,
    INPUT_TOO_SHORT,
};
using DecodeResult = result_t<byte_string_view>;

MONAD_RLP_NAMESPACE_END

BOOST_OUTCOME_SYSTEM_ERROR2_NAMESPACE_BEGIN
template <>
struct quick_status_code_from_enum<monad::rlp::DecodeError>
    : quick_status_code_from_enum_defaults<monad::rlp::DecodeError>
{
    static constexpr auto const domain_name = "Decode Error";
    static constexpr auto const domain_uuid =
        "da6c5e8c-d6a1-101c-9cff-97a0f36ddcb9";
    static std::initializer_list<mapping> const &value_mappings()
    {
        using namespace monad::rlp;
        static const std::initializer_list<mapping> v = {
            {DecodeError::SUCCESS, "Success", {errc::success}},
            {DecodeError::OVERFLOW, "Overflow", {}},
            {DecodeError::UNEXPECTED_LIST, "Unexpected list", {}},
            {DecodeError::UNEXPECTED_LENGTH, "Unexpected length", {}},
            {DecodeError::INPUT_TOO_SHORT, "Input too short", {}},
        };
        return v;
    }
};

BOOST_OUTCOME_SYSTEM_ERROR2_NAMESPACE_END

MONAD_RLP_NAMESPACE_BEGIN

constexpr BOOST_OUTCOME_SYSTEM_ERROR2_NAMESPACE::
    quick_status_code_from_enum_code<DecodeError>
    status_code(DecodeError e)
{
    return e;
}

MONAD_RLP_NAMESPACE_END
