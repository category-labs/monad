// Copyright (C) 2026 Category Labs, Inc.
//
// Generic TinyVM precompile. One class serves all backends.
// Backend logic lives in Rust; this is a thin C++ bridge.
//
// TinyVM forces a fixed operation set (shield, transfer, unshield, etc.)
// that all backends implement. Backends differ in proof format and state
// model, not in operations. This is what allows a single generic precompile.
//
// To add a new backend:
// 1. Implement TinyVmBackend trait in Rust (in monad-tinyvm repo)
// 2. Register it in the Rust FFI registry (tinyvm-confidential-ffi/src/lib.rs)
// 3. Add a CASE line in monad_precompiles.cpp with the new address
// 4. Add the address constant below
// 5. Gate activation behind a new monad_revision
// No new C++ classes or files needed.

#pragma once

#include <category/core/byte_string.hpp>
#include <category/core/config.hpp>
#include <category/core/int.hpp>
#include <category/core/result.hpp>
#include <category/execution/ethereum/core/address.hpp>
#include <category/execution/ethereum/state3/state.hpp>
#include <category/execution/ethereum/trace/call_tracer.hpp>
#include <category/vm/evm/traits.hpp>

#include "tinyvm_error.hpp"

MONAD_NAMESPACE_BEGIN

// Backend precompile addresses.
// TODO: Read address from the Rust backend registry via FFI instead of hardcoding.
// TODO: Add new backend addresses here as they are activated.
// TODO: Use MIP-8 page-based optimisation for storage layout.
inline constexpr Address TINYVM_PRECOMPILE_ADDRESS = Address{0x420};

class TinyVmPrecompile
{
public:
    TinyVmPrecompile(State &state, CallTracerBase &tracer);

    using PrecompileFunc = Result<byte_string> (TinyVmPrecompile::*)(
        byte_string_view, evmc_address const &, evmc_bytes32 const &);

    // All operations route through `execute` — Rust handles dispatch by backend_id.
    template <Traits traits>
    static std::pair<PrecompileFunc, uint64_t>
    precompile_dispatch(byte_string_view &);

private:
    // Generic execute: passes everything to Rust via FFI.
    Result<byte_string> execute(
        byte_string_view input, evmc_address const &msg_sender,
        evmc_uint256be const &msg_value);

    Result<byte_string> precompile_fallback(
        byte_string_view, evmc_address const &, evmc_uint256be const &);

    State &state_;
    CallTracerBase &call_tracer_;
};

MONAD_NAMESPACE_END
