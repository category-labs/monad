#include <bit>

#include <monad/core/c_result.h>
#include <monad/util/parse_util.h>

BOOST_OUTCOME_C_DECLARE_RESULT_SYSTEM_FROM_ENUM(
    monad_strtonum_error, "d04f74ad-4725-4aa1-80ce-71990e4b60b2",
    {monad_strtonum_error::MONAD_STN_BAD_RANGE,
     "[min, max] range is not valid",
     {system_error2::errc::invalid_argument}},
    {monad_strtonum_error::MONAD_STN_NOT_INT_TOKEN,
     "token is not an integer",
     {system_error2::errc::invalid_argument}},
    {monad_strtonum_error::MONAD_STN_TOO_SMALL,
     "value is smaller than minimum",
     {system_error2::errc::result_out_of_range}},
    {monad_strtonum_error::MONAD_STN_TOO_BIG,
     "value is larger than maximum",
     {system_error2::errc::result_out_of_range}});

extern "C" __attribute__((visibility("default"))) monad_c_result
monad_strtonum_make_failure(monad_strtonum_error e)
{
    return outcome_make_result_failure_system_enum_monad_strtonum_error(e);
}

extern "C" __attribute__((visibility("default"))) bool
outcome_status_code_equal_strtonum_error(
    monad_error_code error_code, monad_strtonum_error e)
{
    auto const *const system_code =
        reinterpret_cast<system_error2::system_code *>(&error_code);
    return *system_code ==
           BOOST_OUTCOME_SYSTEM_ERROR2_NAMESPACE::
               quick_status_code_from_enum_code<monad_strtonum_error>{e};
}
