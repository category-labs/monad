#pragma once

#include <monad/core/byte_string.hpp>
#include <monad/core/bytes.hpp>
#include <monad/core/result.hpp>
#include <monad/mpt/nibbles_view.hpp>
#include <monad/mpt2/config.hpp>

// TODO unstable paths between versions
#if __has_include(<boost/outcome/experimental/status-code/status-code/config.hpp>)
    #include <boost/outcome/experimental/status-code/status-code/config.hpp>
    #include <boost/outcome/experimental/status-code/status-code/quick_status_code_from_enum.hpp>
#else
    #include <boost/outcome/experimental/status-code/config.hpp>
    #include <boost/outcome/experimental/status-code/quick_status_code_from_enum.hpp>
#endif

MONAD_MPT2_NAMESPACE_BEGIN

enum class ProofError
{
    Success = 0,
    InvalidKey,
    WrongMerkleProof,
    UnexpectedType,
};

Result<void> verify_proof(
    mpt::NibblesView, mpt::NibblesView, bytes32_t const &, byte_string_view);

MONAD_MPT2_NAMESPACE_END

BOOST_OUTCOME_SYSTEM_ERROR2_NAMESPACE_BEGIN

template <>
struct quick_status_code_from_enum<monad::mpt2::ProofError>
    : quick_status_code_from_enum_defaults<monad::mpt2::ProofError>
{
    static constexpr auto const domain_name = "Proof Error";
    static constexpr auto const domain_uuid =
        "31cf597c-1f17-4e62-87a4-ee278a60b6ad";

    static std::initializer_list<mapping> const &value_mappings();
};

BOOST_OUTCOME_SYSTEM_ERROR2_NAMESPACE_END
