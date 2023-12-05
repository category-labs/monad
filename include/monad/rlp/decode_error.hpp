#pragma once

#include <monad/core/byte_string.hpp>
#include <monad/rlp/config.hpp>

#include <boost/outcome/experimental/status-code/quick_status_code_from_enum.hpp>
#include <boost/outcome/experimental/status_result.hpp>
#include <boost/outcome/try.hpp>

MONAD_RLP_NAMESPACE_BEGIN

enum class DecodeError
{
    Success = 0
};

using decode_result_t =
    boost::outcome_v2::experimental::status_result<byte_string_view>;

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
        static std::initializer_list<mapping> const v = {
            {DecodeError::Success, "Success", {errc::success}},
        };
        return v;
    }
};

BOOST_OUTCOME_SYSTEM_ERROR2_NAMESPACE_END
