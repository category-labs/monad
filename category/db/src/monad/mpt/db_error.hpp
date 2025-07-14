#pragma once

#include <category/core/result.hpp>
#include <monad/mpt/config.hpp>

// TODO unstable paths between versions
#if __has_include(<boost/outcome/experimental/status-code/generic_code.hpp>)
    #include <boost/outcome/experimental/status-code/generic_code.hpp>
#else
    #include <boost/outcome/experimental/status-code/status-code/generic_code.hpp>
#endif

MONAD_MPT_NAMESPACE_BEGIN

enum class DbError : uint8_t
{
    unknown,
    key_not_found,
    version_no_longer_exist,
};

MONAD_MPT_NAMESPACE_END

BOOST_OUTCOME_SYSTEM_ERROR2_NAMESPACE_BEGIN

template <>
struct quick_status_code_from_enum<MONAD_MPT_NAMESPACE::DbError>
    : quick_status_code_from_enum_defaults<MONAD_MPT_NAMESPACE::DbError>
{
    static constexpr auto const domain_name = "DbError domain";

    static constexpr auto const domain_uuid =
        "{975a8e5e-d53f-4a57-304e-0dd4785b4090}";

    static std::initializer_list<mapping> const &value_mappings()
    {
        static std::initializer_list<mapping> const v = {
            {MONAD_MPT_NAMESPACE::DbError::key_not_found, "key not found", {}},
            {MONAD_MPT_NAMESPACE::DbError::unknown, "unknown", {}},
            {MONAD_MPT_NAMESPACE::DbError::version_no_longer_exist,
             "version no longer exists",
             {}},
        };
        return v;
    }
};

BOOST_OUTCOME_SYSTEM_ERROR2_NAMESPACE_END
