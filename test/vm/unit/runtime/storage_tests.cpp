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

#include "fixture.hpp"

#include <category/core/runtime/uint256.hpp>
#include <category/vm/runtime/storage.hpp>
#include <category/vm/runtime/transmute.hpp>

#include <evmc/evmc.h>

using namespace monad;
using namespace monad::vm;
using namespace monad::vm::runtime;
using namespace monad::vm::compiler::test;

namespace
{
    inline constexpr uint256_t key = 6732;
    inline constexpr uint256_t val = 2389;
    inline constexpr uint256_t val_2 = 90897;
}

TEST_F(RuntimeTest, TransientStorage)
{
    auto load = wrap(tload);
    auto store = wrap(tstore);

    ctx_.gas_remaining = 0;

    ASSERT_EQ(load(key), 0);
    ASSERT_EQ(ctx_.result.status, StatusCode::Success);

    store(key, val);
    ASSERT_EQ(ctx_.result.status, StatusCode::Success);
    ASSERT_EQ(load(key), val);
    ASSERT_EQ(ctx_.result.status, StatusCode::Success);

    store(key, val_2);
    ASSERT_EQ(ctx_.result.status, StatusCode::Success);
    ASSERT_EQ(load(key), val_2);
    ASSERT_EQ(ctx_.result.status, StatusCode::Success);
}

TYPED_TEST(RuntimeTraitsTest, StorageLoadCold)
{
    using traits = TestFixture::Trait;
    auto load = TestFixture::wrap(sload<traits>);

    this->ctx_.gas_remaining = [] {
        if constexpr (is_monad_trait_v<traits>) {
            if constexpr (traits::monad_rev() >= MONAD_SEVEN) {
                return 8000;
            }
        }
        if constexpr (traits::evm_rev() <= EVMC_ISTANBUL) {
            return 0;
        }
        else {
            return 2000;
        }
    }();
    ASSERT_EQ(load(key), 0);
    ASSERT_EQ(this->ctx_.result.status, StatusCode::Success);
    ASSERT_EQ(this->ctx_.gas_remaining, 0);
    ASSERT_EQ(load(key), 0);
    ASSERT_EQ(this->ctx_.result.status, StatusCode::Success);
    ASSERT_EQ(this->ctx_.gas_remaining, 0);
}

TYPED_TEST(RuntimeTraitsTest, StorageLoadWarm)
{
    using traits = TestFixture::Trait;
    auto load = TestFixture::wrap(sload<traits>);

    this->host_.access_storage(
        this->ctx_.env.recipient, bytes32_from_uint256(key));

    this->ctx_.gas_remaining = 0;
    ASSERT_EQ(load(key), 0);
    ASSERT_EQ(this->ctx_.result.status, StatusCode::Success);
    ASSERT_EQ(this->ctx_.gas_remaining, 0);
}

TYPED_TEST(RuntimeTraitsTest, StorageOriginalEmpty)
{
    using traits = TestFixture::Trait;
    auto load = TestFixture::wrap(sload<traits>);
    auto store = TestFixture::wrap(sstore<traits>);

    auto do_test = [&load, &store, &ctx_ = this->ctx_](
                       int64_t empty_nonempty_cold_cost,
                       int64_t nonempty_empty_warm_refund) {
        // empty -> nonempty (cold)
        ctx_.gas_remaining = empty_nonempty_cold_cost;
        store(key, val);
        ASSERT_EQ(ctx_.gas_remaining, 0);
        ASSERT_EQ(load(key), val);
        ASSERT_EQ(ctx_.result.status, StatusCode::Success);

        // nonempty -> nonempty (warm)
        ctx_.gas_remaining = 2301;
        store(key, val_2);
        ASSERT_EQ(ctx_.result.status, StatusCode::Success);
        ASSERT_EQ(ctx_.gas_remaining, 2301);
        ASSERT_EQ(load(key), val_2);
        ASSERT_EQ(ctx_.result.status, StatusCode::Success);

        // nonempty -> empty (warm)
        ctx_.gas_remaining = 2301;
        store(key, 0);
        ASSERT_EQ(ctx_.result.status, StatusCode::Success);
        ASSERT_EQ(ctx_.gas_remaining, 2301);
        ASSERT_EQ(ctx_.gas_refund, nonempty_empty_warm_refund);
        ASSERT_EQ(load(key), 0);
        ASSERT_EQ(ctx_.result.status, StatusCode::Success);
    };

    if constexpr (is_monad_trait_v<traits>) {
        if constexpr (traits::monad_rev() >= MONAD_SEVEN) {
            return do_test(28000, 19900);
        }
    }
    if constexpr (
        traits::evm_rev() <= EVMC_BYZANTIUM ||
        traits::evm_rev() == EVMC_PETERSBURG) {
        do_test(15000, 15000);
    }
    else if constexpr (traits::evm_rev() == EVMC_CONSTANTINOPLE) {
        do_test(19800, 19800);
    }
    else if constexpr (traits::evm_rev() == EVMC_ISTANBUL) {
        do_test(19200, 19200);
    }
    else {
        do_test(22000, 19900);
    }
}

TYPED_TEST(RuntimeTraitsTest, StorageOriginalNonEmpty)
{
    using traits = TestFixture::Trait;
    auto load = TestFixture::wrap(sload<traits>);
    auto store = TestFixture::wrap(sstore<traits>);

    // current == original
    auto &loc = this->host_.accounts[this->ctx_.env.recipient]
                    .storage[bytes32_from_uint256(key)];
    loc.original = bytes32_from_uint256(val);
    loc.current = bytes32_from_uint256(val);

    auto do_test = [&load, &store, &ctx_ = this->ctx_](
                       int64_t nonempty_same_nonempty_cold_remaining,
                       int64_t nonempty_different_nonempty_warm_cost) {
        // nonempty -> same nonempty (cold)
        ctx_.gas_remaining = 8100;
        store(key, val);
        ASSERT_EQ(ctx_.result.status, StatusCode::Success);
        ASSERT_EQ(ctx_.gas_remaining, nonempty_same_nonempty_cold_remaining);
        ASSERT_EQ(load(key), val);
        ASSERT_EQ(ctx_.result.status, StatusCode::Success);

        // nonempty -> different nonempty (warm)
        ctx_.gas_remaining = nonempty_different_nonempty_warm_cost;
        store(key, val_2);
        ASSERT_EQ(ctx_.result.status, StatusCode::Success);
        ASSERT_EQ(ctx_.gas_remaining, 0);
        ASSERT_EQ(load(key), val_2);
        ASSERT_EQ(ctx_.result.status, StatusCode::Success);

        // nonempty -> empty (warm)
        ctx_.gas_remaining = 2301;
        store(key, 0);
        ASSERT_EQ(ctx_.result.status, StatusCode::Success);
        ASSERT_EQ(ctx_.gas_remaining, 2301);
        if constexpr (traits::evm_rev() <= EVMC_BERLIN) {
            ASSERT_EQ(ctx_.gas_refund, 15000);
        }
        else {
            ASSERT_EQ(ctx_.gas_refund, 4800);
        }
        ASSERT_EQ(load(key), 0);
        ASSERT_EQ(ctx_.result.status, StatusCode::Success);
    };

    if constexpr (is_monad_trait_v<traits>) {
        if constexpr (traits::monad_rev() >= MONAD_SEVEN) {
            return do_test(0, 2800);
        }
    }
    if constexpr (
        traits::evm_rev() <= EVMC_BYZANTIUM ||
        traits::evm_rev() == EVMC_PETERSBURG) {
        do_test(8100, 0);
    }
    else if constexpr (traits::evm_rev() == EVMC_CONSTANTINOPLE) {
        do_test(8100, 4800);
    }
    else if constexpr (traits::evm_rev() == EVMC_ISTANBUL) {
        do_test(8100, 4200);
    }
    else {
        do_test(6000, 2800);
    }
}
