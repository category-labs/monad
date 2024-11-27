#include <monad/config.hpp>
#include <monad/rpc/error.hpp>

#include <boost/outcome/config.hpp>
// TODO unstable paths between versions
#if __has_include(<boost/outcome/experimental/status-code/status-code/config.hpp>)
    #include <boost/outcome/experimental/status-code/status-code/config.hpp>
    #include <boost/outcome/experimental/status-code/status-code/generic_code.hpp>
#else
    #include <boost/outcome/experimental/status-code/config.hpp>
    #include <boost/outcome/experimental/status-code/generic_code.hpp>
#endif
#include <boost/outcome/success_failure.hpp>

#include <initializer_list>

BOOST_OUTCOME_SYSTEM_ERROR2_NAMESPACE_BEGIN

std::initializer_list<
    quick_status_code_from_enum<monad::RpcError>::mapping> const &
quick_status_code_from_enum<monad::RpcError>::value_mappings()
{
    using monad::RpcError;

    static std::initializer_list<mapping> const v = {
        {RpcError::Success, "success", {errc::success}},
        {RpcError::EthCallBlockHashBufferError,
         "eth_call unable to initialize BlockHashBuffer",
         {}}};

    return v;
}

BOOST_OUTCOME_SYSTEM_ERROR2_NAMESPACE_END
