#pragma once

#include <monad/config.hpp>

// TODO unstable paths between versions
#if __has_include(<boost/outcome/experimental/status-code/status-code/config.hpp>)
    #include <boost/outcome/experimental/status-code/status-code/config.hpp>
    #include <boost/outcome/experimental/status-code/status-code/quick_status_code_from_enum.hpp>
#else
    #include <boost/outcome/experimental/status-code/config.hpp>
    #include <boost/outcome/experimental/status-code/quick_status_code_from_enum.hpp>
#endif

#include <initializer_list>
#include <optional>

MONAD_NAMESPACE_BEGIN

enum class RpcError
{
    Success = 0,
    EthCallBlockHashBufferError,
};

MONAD_NAMESPACE_END

BOOST_OUTCOME_SYSTEM_ERROR2_NAMESPACE_BEGIN

template <>
struct quick_status_code_from_enum<monad::RpcError>
    : quick_status_code_from_enum_defaults<monad::RpcError>
{
    static constexpr auto const domain_name = "Rpc Error";
    static constexpr auto const domain_uuid =
        "01942e1bbe127b99af4519243f52042e12ce";

    static std::initializer_list<mapping> const &value_mappings();
};

BOOST_OUTCOME_SYSTEM_ERROR2_NAMESPACE_END
