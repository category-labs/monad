#pragma once

#include <category/core/config.hpp>
#include <category/core/result.hpp>

// TODO unstable paths between versions
#if __has_include(<boost/outcome/experimental/status-code/status-code/config.hpp>)
    #include <boost/outcome/experimental/status-code/status-code/config.hpp>
    #include <boost/outcome/experimental/status-code/status-code/quick_status_code_from_enum.hpp>
#else
    #include <boost/outcome/experimental/status-code/config.hpp>
    #include <boost/outcome/experimental/status-code/quick_status_code_from_enum.hpp>
#endif

MONAD_NAMESPACE_BEGIN

enum class MonadBlockError
{
    Success = 0,
    TimestampMismatch,
};

template <class MonadConsensusBlockHeader>
Result<void>
static_validate_consensus_header(MonadConsensusBlockHeader const &);

MONAD_NAMESPACE_END

BOOST_OUTCOME_SYSTEM_ERROR2_NAMESPACE_BEGIN

template <>
struct quick_status_code_from_enum<monad::MonadBlockError>
    : quick_status_code_from_enum_defaults<monad::MonadBlockError>
{
    static constexpr auto const domain_name = "Monad Block Error";
    static constexpr auto const domain_uuid =
        "6eb636da00ddd479646eeb39b8168c814cb4";

    static std::initializer_list<mapping> const &value_mappings();
};

BOOST_OUTCOME_SYSTEM_ERROR2_NAMESPACE_END
