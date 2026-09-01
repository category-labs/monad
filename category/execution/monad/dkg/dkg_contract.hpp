// Copyright (C) 2026 Category Labs, Inc.

#pragma once

#include <category/core/address.hpp>
#include <category/core/byte_string.hpp>
#include <category/core/bytes.hpp>
#include <category/core/config.hpp>
#include <category/core/int.hpp>
#include <category/core/result.hpp>
#include <category/execution/ethereum/trace/call_tracer.hpp>
#include <category/vm/evm/traits.hpp>

#include <cstdint>
#include <utility>

MONAD_NAMESPACE_BEGIN

class State;

namespace dkg
{

    using namespace monad::literals;

    inline constexpr Address DKG_CA{0x1002};

    // DKG lifecycle transitions are driven only by authenticated execution
    // hooks, matching native staking. User calls verify this state but never
    // rotate or initialize it.
    bool initialize_states(State &);
    bool on_staking_snapshot(State &, uint64_t next_epoch);
    bool on_staking_epoch_change(State &, uint64_t current_epoch);

    class DkgContract
    {
    public:
        using PrecompileFunc = Result<byte_string> (DkgContract::*)(
            byte_string_view, Address const &, uint256_be_t const &);

        struct Dispatch
        {
            PrecompileFunc method;
            uint64_t gas_cost;
            bool read_only;
        };

        DkgContract(State &, CallTracerBase &, uint64_t block_number = 0);

        template <Traits traits>
        static Dispatch precompile_dispatch(byte_string_view &);

        Result<byte_string> precompile_register(
            byte_string_view, Address const &, uint256_be_t const &);
        Result<byte_string> precompile_post_pc_qc(
            byte_string_view, Address const &, uint256_be_t const &);
        Result<byte_string> precompile_post_bve_qc(
            byte_string_view, Address const &, uint256_be_t const &);
        Result<byte_string> precompile_submit_result(
            byte_string_view, Address const &, uint256_be_t const &);
        Result<byte_string> precompile_registration_of(
            byte_string_view, Address const &, uint256_be_t const &);
        Result<byte_string> precompile_pc_qcs(
            byte_string_view, Address const &, uint256_be_t const &);
        Result<byte_string> precompile_bve_qcs(
            byte_string_view, Address const &, uint256_be_t const &);
        Result<byte_string> precompile_dkg_result(
            byte_string_view, Address const &, uint256_be_t const &);
        Result<byte_string> precompile_fallback(
            byte_string_view, Address const &, uint256_be_t const &);

    private:
        State &state_;
        CallTracerBase &call_tracer_;
        uint64_t block_number_;
    };

} // namespace dkg

MONAD_NAMESPACE_END
