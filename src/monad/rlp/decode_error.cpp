#include <monad/core/result.hpp>
#include <monad/rlp/config.hpp>
#include <monad/rlp/decode_error.hpp>

#include <boost/outcome/config.hpp>
#include <boost/outcome/experimental/status-code/quick_status_code_from_enum.hpp>

#include <boost/outcome/success_failure.hpp>

#include <initializer_list>

BOOST_OUTCOME_SYSTEM_ERROR2_NAMESPACE_BEGIN

std::initializer_list<
    quick_status_code_from_enum<monad::rlp::DecodeError>::mapping> const &
quick_status_code_from_enum<monad::rlp::DecodeError>::value_mappings()
{
    using monad::rlp::DecodeError;

    static std::initializer_list<mapping> const v = {
        {DecodeError::Success, "success", {errc::success}},
        {DecodeError::TypeUnexpected, "type unexpected", {}},
        {DecodeError::Overflow, "overflow", {}},
        {DecodeError::InputTooLong, "input too long", {}},
        {DecodeError::InputTooShort, "input too short", {}},
        {DecodeError::ArrayLengthUnexpected, "array length unexpected", {}},
        {DecodeError::InvalidTxnType, "invalid txn type", {}},
        {DecodeError::LeadingZero, "leading zero", {}},
    };

    return v;
}

BOOST_OUTCOME_SYSTEM_ERROR2_NAMESPACE_END
