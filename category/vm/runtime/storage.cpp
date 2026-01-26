// Copyright (C) 2025 Category Labs, Inc.
//
// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with this program.  If not, see <http://www.gnu.org/licenses/>.

#include <category/core/runtime/uint256.hpp>
#include <category/vm/runtime/storage.hpp>
#include <category/vm/runtime/types.hpp>

#include <cstdint>

#include <cstring>
#include <evmc/evmc.h>
#include <evmc/evmc.hpp>

#ifdef MONAD_COMPILER_TESTING
    #include <category/core/bytes.hpp>
    #include <category/execution/ethereum/core/address.hpp>
    #include <category/vm/runtime/transmute.hpp>
    #include <map>
    #include <tuple>
#else
    #include <exception>
#endif

namespace monad::vm::runtime
{
#ifdef MONAD_COMPILER_TESTING
    bool debug_tstore_stack(
        Context const *ctx, uint256_t const *stack, uint64_t stack_size,
        uint64_t offset, uint64_t base_offset)
    {
        auto const magic = uint256_t{0xdeb009};
        auto const base = (magic + base_offset) * 1024;
        if (offset == 0) {
            auto const base_key = bytes32_from_uint256(base);
            auto const base_value = ctx->host->get_transient_storage(
                ctx->context, &ctx->env.recipient, &base_key);
            if (base_value != evmc::bytes32{}) {
                // If this transient storage location has already been written,
                // then we are likely in a loop. We return early in this case
                // to avoid repeatedly saving stack to transient storage.
                return false;
            }
        }
        for (uint64_t i = 0; i < stack_size; ++i) {
            auto const key = bytes32_from_uint256(base + i + offset);
            auto const &x = stack[static_cast<int64_t>(-i) - 1];
            // Make sure we do not store zero, because incorrect non-zero is
            // more likely to be noticed, due to zero being the default:
            auto const s = x < magic ? x + 1 : x;
            auto const value = bytes32_from_uint256(s);
            ctx->host->set_transient_storage(
                ctx->context, &ctx->env.recipient, &key, &value);
        }
        return true;
    }
#else
    bool debug_tstore_stack(
        Context const *, uint256_t const *, uint64_t, uint64_t, uint64_t)
    {
        std::terminate();
    }
#endif
}

#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wsign-conversion"
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wdeprecated-declarations"

#ifdef MONAD_COMPILER_TESTING
// In test mode, we use a simple in-memory map for block storage

namespace monad::vm::runtime
{
    // Static map for test block storage
    static std::map<
        std::tuple<::monad::Address, ::monad::bytes32_t>, ::monad::bytes4k_t> &
    get_test_block_storage()
    {
        static std::map<
            std::tuple<::monad::Address, ::monad::bytes32_t>,
            ::monad::bytes4k_t>
            storage;
        return storage;
    }

    ::monad::bytes4k_t get_block_storage_from_context(
        evmc_host_context *context, ::monad::Address const &recipient,
        ::monad::bytes32_t const &key)
    {
        (void)context; // Unused in test mode
        auto &storage = get_test_block_storage();
        auto const it = storage.find(std::make_tuple(recipient, key));
        if (it != storage.end()) {
            return it->second;
        }
        // Return zeroed block if not found
        ::monad::bytes4k_t result{};
        std::memset(result.bytes, 0, sizeof(result.bytes));
        return result;
    }

    void set_block_storage_from_context(
        evmc_host_context *context, ::monad::Address const &recipient,
        ::monad::bytes32_t const &key, ::monad::bytes4k_t const &value)
    {
        (void)context; // Unused in test mode
        auto &storage = get_test_block_storage();
        storage[std::make_tuple(recipient, key)] = value;
    }

    void clear_test_block_storage()
    {
        auto &storage = get_test_block_storage();
        storage.clear();
    }
}
#else
    // In production mode, use EvmcHostBase
    #include <category/execution/ethereum/core/address.hpp>
    #include <category/execution/ethereum/evmc_host.hpp>

namespace monad::vm::runtime
{
    ::monad::bytes4k_t get_block_storage_from_context(
        evmc_host_context *context, ::monad::Address const &recipient,
        ::monad::bytes32_t const &key)
    {
        auto *host = reinterpret_cast<monad::EvmcHostBase *>(context);
        return host->get_block_storage(recipient, key);
    }

    void set_block_storage_from_context(
        evmc_host_context *context, ::monad::Address const &recipient,
        ::monad::bytes32_t const &key, ::monad::bytes4k_t const &value)
    {
        auto *host = reinterpret_cast<monad::EvmcHostBase *>(context);
        host->set_block_storage(recipient, key, value);
    }
}
#endif

#pragma GCC diagnostic pop
