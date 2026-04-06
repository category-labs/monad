// Copyright (C) 2026 Category Labs, Inc.

#pragma once

#include <category/core/config.hpp>
#include <category/core/result.hpp>
#include <system_error>

// TODO unstable paths between versions
#if __has_include(<boost/outcome/experimental/status-code/status-code/config.hpp>)
    #include <boost/outcome/experimental/status-code/status-code/config.hpp>
    #include <boost/outcome/experimental/status-code/status-code/quick_status_code_from_enum.hpp>
#else
    #include <boost/outcome/experimental/status-code/config.hpp>
    #include <boost/outcome/experimental/status-code/quick_status_code_from_enum.hpp>
#endif

#include <initializer_list>

MONAD_NAMESPACE_BEGIN

enum class TinyVmPrecompileError
{
    Success = 0,
    MethodNotSupported,
    InvalidInput,
    VerificationFailed,
};

MONAD_NAMESPACE_END

BOOST_OUTCOME_SYSTEM_ERROR2_NAMESPACE_BEGIN
template <>
struct quick_status_code_from_enum<monad::TinyVmPrecompileError>
    : quick_status_code_from_enum_defaults<monad::TinyVmPrecompileError>
{
    static constexpr auto const domain_name = "tinyvm precompile error";
    static constexpr auto const domain_uuid =
        "6f0ed8f1-7df8-4ca8-b747-8ff2b56f4e91";
    using Base = quick_status_code_from_enum_defaults<monad::TinyVmPrecompileError>;
    using mapping = Base::mapping;
    static inline std::initializer_list<mapping> const &value_mappings()
    {
        using monad::TinyVmPrecompileError;
        static std::initializer_list<mapping> const v = {
            {TinyVmPrecompileError::Success, "success", {errc::success}},
            {TinyVmPrecompileError::MethodNotSupported, "method not supported", {}},
            {TinyVmPrecompileError::InvalidInput, "input is invalid", {}},
            {TinyVmPrecompileError::VerificationFailed, "verification failed", {}},
        };
        return v;
    }
};
BOOST_OUTCOME_SYSTEM_ERROR2_NAMESPACE_END
