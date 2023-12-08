#pragma once

#include <monad/rlp/config.hpp>

#include <boost/outcome/config.hpp>
#include <boost/outcome/experimental/status-code/quick_status_code_from_enum.hpp>

#include <initializer_list>

MONAD_RLP_NAMESPACE_BEGIN

enum class DecodeError
{
    Success = 0,
    TypeUnexpected,
    Overflow,
    InputTooLong,
    InputTooShort,
    ArrayLengthUnexpected,
};

MONAD_RLP_NAMESPACE_END

BOOST_OUTCOME_SYSTEM_ERROR2_NAMESPACE_BEGIN

template <>
struct quick_status_code_from_enum<monad::rlp::DecodeError>
    : quick_status_code_from_enum_defaults<monad::rlp::DecodeError>
{
    static constexpr auto const domain_name = "Decode Error";
    static constexpr auto const domain_uuid =
        "da6c5e8c-d6a1-101c-9cff-97a0f36ddcb9";

    static std::initializer_list<mapping> const &value_mappings();
};

BOOST_OUTCOME_SYSTEM_ERROR2_NAMESPACE_END
