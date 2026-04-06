// Copyright (C) 2026 Category Labs, Inc.
//
// Generic TinyVM precompile. Delegates all logic to Rust via FFI.

#include <category/core/keccak.hpp>
#include <category/execution/monad/tinyvm/tinyvm_precompile.hpp>
#include <category/execution/monad/tinyvm/tinyvm_ffi.h>
#include <category/execution/ethereum/core/contract/abi_encode.hpp>
#include <category/execution/ethereum/core/receipt.hpp>
#include <category/vm/evm/explicit_traits.hpp>

#include <boost/outcome/try.hpp>
#include <array>
#include <cstring>
#include <limits>

MONAD_ANONYMOUS_NAMESPACE_BEGIN

constexpr uint64_t TINYVM_FALLBACK_COST = 100;
constexpr size_t ERROR_BUF_LEN = 256;

// Bridge C++ State to Rust TinyVmStateStore via FFI callbacks.
// Rust values may exceed 32 bytes (bincode-serialized structs), so we
// spread them across consecutive EVM storage slots:
//   base_slot   = keccak256(key)  → stores value length as uint256
//   base_slot+1 = first 32-byte chunk of value
//   base_slot+2 = second chunk ...
struct StoreContext
{
    monad::State *state;
    monad::Address const *precompile_addr;
};

monad::bytes32_t key_to_base_slot(uint8_t const *key, size_t key_len)
{
    return monad::to_bytes(
        monad::keccak256(monad::byte_string_view{key, key_len}));
}

monad::bytes32_t slot_plus(monad::bytes32_t const &base, size_t offset)
{
    auto val = intx::be::load<monad::uint256_t>(base);
    val += offset;
    monad::bytes32_t out{};
    intx::be::store(out.bytes, val);
    return out;
}

int store_get_callback(
    void *ctx,
    uint8_t const *key, size_t key_len,
    uint8_t *value_buf, size_t value_buf_len,
    size_t *value_len)
{
    auto *sc = static_cast<StoreContext *>(ctx);
    auto const base = key_to_base_slot(key, key_len);

    // Slot 0: stored length
    auto const len_slot = sc->state->get_storage(*sc->precompile_addr, base);
    auto const stored_len = static_cast<size_t>(
        intx::be::load<monad::uint256_t>(len_slot));

    if (stored_len == 0) {
        *value_len = 0;
        return 0; // key not found
    }

    size_t const copy_len = std::min(stored_len, value_buf_len);
    size_t const num_chunks = (stored_len + 31) / 32;

    for (size_t i = 0; i < num_chunks; ++i) {
        auto const chunk_slot = slot_plus(base, i + 1);
        auto const chunk = sc->state->get_storage(*sc->precompile_addr, chunk_slot);
        size_t const offset = i * 32;
        size_t const chunk_copy = std::min<size_t>(32, copy_len - std::min(offset, copy_len));
        if (chunk_copy > 0) {
            std::memcpy(value_buf + offset, chunk.bytes, chunk_copy);
        }
    }

    *value_len = copy_len;
    return 1;
}

void store_set_callback(
    void *ctx,
    uint8_t const *key, size_t key_len,
    uint8_t const *value, size_t value_len)
{
    auto *sc = static_cast<StoreContext *>(ctx);
    auto const base = key_to_base_slot(key, key_len);

    // Slot 0: store length
    monad::bytes32_t len_val{};
    intx::be::store(len_val.bytes, monad::uint256_t{value_len});
    sc->state->set_storage(*sc->precompile_addr, base, len_val);

    // Slots 1..N: store 32-byte chunks
    size_t const num_chunks = (value_len + 31) / 32;
    for (size_t i = 0; i < num_chunks; ++i) {
        monad::bytes32_t chunk{};
        size_t const offset = i * 32;
        size_t const chunk_len = std::min<size_t>(32, value_len - offset);
        std::memcpy(chunk.bytes, value + offset, chunk_len);
        sc->state->set_storage(*sc->precompile_addr, slot_plus(base, i + 1), chunk);
    }
}

MONAD_ANONYMOUS_NAMESPACE_END

MONAD_NAMESPACE_BEGIN

TinyVmPrecompile::TinyVmPrecompile(State &state, CallTracerBase &tracer)
    : state_{state}
    , call_tracer_{tracer}
{
    // Ensure the precompile account exists in the state trie.
    // Must be non-zero to survive EIP-161 empty account cleanup.
    if (state_.get_balance(TINYVM_PRECOMPILE_ADDRESS) == 0) {
        state_.add_to_balance(TINYVM_PRECOMPILE_ADDRESS, 1);
    }
}

template <Traits traits>
std::pair<TinyVmPrecompile::PrecompileFunc, uint64_t>
TinyVmPrecompile::precompile_dispatch(byte_string_view &input)
{
    uint64_t cost = tinyvm_gas_cost(input.data(), input.size());
    if (cost == 0) {
        return {&TinyVmPrecompile::precompile_fallback, TINYVM_FALLBACK_COST};
    }
    return {&TinyVmPrecompile::execute, cost};
}

EXPLICIT_MONAD_TRAITS(TinyVmPrecompile::precompile_dispatch);

Result<byte_string> TinyVmPrecompile::execute(
    byte_string_view input, evmc_address const &msg_sender,
    evmc_uint256be const &msg_value)
{
    // Decode tx.value as u128 (lo + hi u64 halves)
    auto const native = intx::be::load<uint256_t>(msg_value);
    if (MONAD_UNLIKELY(native >> 128 != 0)) {
        return TinyVmPrecompileError::InvalidInput;
    }
    uint64_t const val_lo = static_cast<uint64_t>(native & 0xFFFFFFFFFFFFFFFF);
    uint64_t const val_hi = static_cast<uint64_t>((native >> 64) & 0xFFFFFFFFFFFFFFFF);

    // Set up store callbacks bridging Rust → C++ State
    StoreContext store_ctx{&state_, &TINYVM_PRECOMPILE_ADDRESS};
    tinyvm_apply_result result{};
    std::array<char, ERROR_BUF_LEN> error_buf{};
    constexpr size_t LOGS_BUF_LEN = 4096; // ~25 logs per tx at ~160 bytes each
    std::array<uint8_t, LOGS_BUF_LEN> logs_buf{};
    size_t logs_written = 0;

    auto const rc = tinyvm_apply(
        msg_sender.bytes, sizeof(msg_sender.bytes),
        val_lo, val_hi,
        input.data(), input.size(),
        &store_ctx,
        store_get_callback,
        store_set_callback,
        &result,
        logs_buf.data(), logs_buf.size(), &logs_written,
        error_buf.data(), error_buf.size());

    if (rc != 1 || !result.success) {
        return TinyVmPrecompileError::VerificationFailed;
    }

    // Apply escrow refund (unshield only)
    uint256_t refund = static_cast<unsigned __int128>(result.escrow_refund);
    if (refund > 0) {
        Address owner{};
        std::memcpy(owner.bytes, result.owner, sizeof(owner.bytes));
        state_.add_to_balance(owner, refund);
        state_.subtract_from_balance(TINYVM_PRECOMPILE_ADDRESS, refund);
    }

    // Emit EVM log events from serialized log buffer.
    // Format: [num_logs: u32 LE] { [num_topics: u32 LE] [topics: 32B each] [data_len: u32 LE] [data] }*
    if (logs_written >= 4) {
        uint8_t const *p = logs_buf.data();
        uint8_t const *end = p + logs_written;
        uint32_t num_logs = 0;
        std::memcpy(&num_logs, p, 4); p += 4;

        for (uint32_t i = 0; i < num_logs && p + 4 <= end; ++i) {
            Receipt::Log log;
            log.address = TINYVM_PRECOMPILE_ADDRESS;

            uint32_t num_topics = 0;
            std::memcpy(&num_topics, p, 4); p += 4;

            for (uint32_t t = 0; t < num_topics && p + 32 <= end; ++t) {
                bytes32_t topic{};
                std::memcpy(topic.bytes, p, 32); p += 32;
                log.topics.push_back(topic);
            }

            if (p + 4 > end) break;
            uint32_t data_len = 0;
            std::memcpy(&data_len, p, 4); p += 4;

            if (p + data_len <= end) {
                log.data.assign(p, p + data_len);
                p += data_len;
            }

            state_.store_log(log);
            call_tracer_.on_log(log);
        }
    }

    return byte_string{abi_encode_bool(true)};
}

Result<byte_string> TinyVmPrecompile::precompile_fallback(
    byte_string_view, evmc_address const &, evmc_uint256be const &)
{
    return TinyVmPrecompileError::MethodNotSupported;
}

MONAD_NAMESPACE_END
