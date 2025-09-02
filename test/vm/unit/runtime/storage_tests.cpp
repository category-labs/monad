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

#include <category/vm/runtime/storage.hpp>
#include <category/vm/runtime/transmute.hpp>
#include <category/vm/runtime/uint256.hpp>

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

    store(key, val);
    ASSERT_EQ(load(key), val);

    store(key, val_2);
    ASSERT_EQ(load(key), val_2);
}

TEST_F(RuntimeTest, StorageHomestead)
{
    using traits = EvmTraits<EVMC_HOMESTEAD>;
    auto load = wrap(sload<traits>);
    auto store = wrap(sstore<traits>);

    ctx_.gas_remaining = 0;
    ASSERT_EQ(load(key), 0);

    ctx_.gas_remaining = 15000;
    store(key, val);
    ASSERT_EQ(ctx_.gas_remaining, 0);
    ASSERT_EQ(load(key), val);

    ctx_.gas_remaining = 0;
    store(key, val_2);
    ASSERT_EQ(ctx_.gas_remaining, 0);
    ASSERT_EQ(load(key), val_2);

    ctx_.gas_remaining = 0;
    store(key, 0);
    ASSERT_EQ(ctx_.gas_remaining, 0);
    ASSERT_EQ(ctx_.gas_refund, 15000);
    ASSERT_EQ(load(key), 0);
}

TEST_F(RuntimeTest, StorageConstantinopleOriginalEmpty)
{
    using traits = EvmTraits<EVMC_CONSTANTINOPLE>;
    auto load = wrap(sload<traits>);
    auto store = wrap(sstore<traits>);

    ctx_.gas_remaining = 0;
    ASSERT_EQ(load(key), 0);

    // empty -> nonempty
    ctx_.gas_remaining = 19800;
    store(key, val);
    ASSERT_EQ(ctx_.gas_remaining, 0);
    ASSERT_EQ(load(key), val);

    // nonempty -> nonempty
    ctx_.gas_remaining = 0;
    store(key, val_2);
    ASSERT_EQ(ctx_.gas_remaining, 0);
    ASSERT_EQ(load(key), val_2);

    // nonempty -> empty
    ctx_.gas_remaining = 0;
    store(key, 0);
    ASSERT_EQ(ctx_.gas_remaining, 0);
    ASSERT_EQ(ctx_.gas_refund, 19800);
    ASSERT_EQ(load(key), 0);
}

TEST_F(RuntimeTest, StorageConstantinopleOriginalNonEmpty)
{
    using traits = EvmTraits<EVMC_CONSTANTINOPLE>;
    auto load = wrap(sload<traits>);
    auto store = wrap(sstore<traits>);

    // current == original
    auto &loc =
        host_.accounts[ctx_.env.recipient].storage[bytes32_from_uint256(key)];
    loc.original = bytes32_from_uint256(val);
    loc.current = bytes32_from_uint256(val);

    ctx_.gas_remaining = 0;
    ASSERT_EQ(load(key), val);

    // nonempty -> same nonempty
    ctx_.gas_remaining = 0;
    store(key, val);
    ASSERT_EQ(ctx_.gas_remaining, 0);
    ASSERT_EQ(load(key), val);

    // nonempty -> different nonempty
    ctx_.gas_remaining = 4800;
    store(key, val_2);
    ASSERT_EQ(ctx_.gas_remaining, 0);
    ASSERT_EQ(load(key), val_2);

    // nonempty -> empty
    ctx_.gas_remaining = 0;
    store(key, 0);
    ASSERT_EQ(ctx_.gas_remaining, 0);
    ASSERT_EQ(ctx_.gas_refund, 15000);
    ASSERT_EQ(load(key), 0);
}

TEST_F(RuntimeTest, StorageIstanbulOriginalEmpty)
{
    using traits = EvmTraits<EVMC_ISTANBUL>;
    auto load = wrap(sload<traits>);
    auto store = wrap(sstore<traits>);

    ctx_.gas_remaining = 0;
    ASSERT_EQ(load(key), 0);

    // empty -> nonempty
    ctx_.gas_remaining = 19200;
    store(key, val);
    ASSERT_EQ(ctx_.gas_remaining, 0);
    ASSERT_EQ(load(key), val);

    // nonempty -> nonempty
    ctx_.gas_remaining = 2301;
    store(key, val_2);
    ASSERT_EQ(ctx_.gas_remaining, 2301);
    ASSERT_EQ(load(key), val_2);

    // nonempty -> empty
    ctx_.gas_remaining = 2301;
    store(key, 0);
    ASSERT_EQ(ctx_.gas_remaining, 2301);
    ASSERT_EQ(ctx_.gas_refund, 19200);
    ASSERT_EQ(load(key), 0);
}

TEST_F(RuntimeTest, StorageIstanbulOriginalNonEmpty)
{
    using traits = EvmTraits<EVMC_ISTANBUL>;
    auto load = wrap(sload<traits>);
    auto store = wrap(sstore<traits>);

    // current == original
    auto &loc =
        host_.accounts[ctx_.env.recipient].storage[bytes32_from_uint256(key)];
    loc.original = bytes32_from_uint256(val);
    loc.current = bytes32_from_uint256(val);

    ctx_.gas_remaining = 0;
    ASSERT_EQ(load(key), val);

    // nonempty -> same nonempty
    ctx_.gas_remaining = 2301;
    store(key, val);
    ASSERT_EQ(ctx_.gas_remaining, 2301);
    ASSERT_EQ(load(key), val);

    // nonempty -> different nonempty
    ctx_.gas_remaining = 4200;
    store(key, val_2);
    ASSERT_EQ(ctx_.gas_remaining, 0);
    ASSERT_EQ(load(key), val_2);

    // nonempty -> empty
    ctx_.gas_remaining = 2301;
    store(key, 0);
    ASSERT_EQ(ctx_.gas_remaining, 2301);
    ASSERT_EQ(ctx_.gas_refund, 15000);
    ASSERT_EQ(load(key), 0);
}

TEST_F(RuntimeTest, StorageBerlinLoadCold)
{
    using traits = EvmTraits<EVMC_BERLIN>;
    auto load = wrap(sload<traits>);

    ctx_.gas_remaining = 2000;
    ASSERT_EQ(load(key), 0);
    ASSERT_EQ(ctx_.gas_remaining, 0);
    ASSERT_EQ(load(key), 0);
    ASSERT_EQ(ctx_.gas_remaining, 0);
}

TEST_F(RuntimeTest, StorageBerlinLoadWarm)
{
    using traits = EvmTraits<EVMC_BERLIN>;
    auto load = wrap(sload<traits>);

    host_.access_storage(ctx_.env.recipient, bytes32_from_uint256(key));

    ctx_.gas_remaining = 0;
    ASSERT_EQ(load(key), 0);
    ASSERT_EQ(ctx_.gas_remaining, 0);
}

TEST_F(RuntimeTest, StorageBerlinOriginalEmpty)
{
    using traits = EvmTraits<EVMC_BERLIN>;
    auto load = wrap(sload<traits>);
    auto store = wrap(sstore<traits>);

    // empty -> nonempty (cold)
    ctx_.gas_remaining = 22000;
    store(key, val);
    ASSERT_EQ(ctx_.gas_remaining, 0);
    ASSERT_EQ(load(key), val);

    // nonempty -> nonempty (warm)
    ctx_.gas_remaining = 2301;
    store(key, val_2);
    ASSERT_EQ(ctx_.gas_remaining, 2301);
    ASSERT_EQ(load(key), val_2);

    // nonempty -> empty (warm)
    ctx_.gas_remaining = 2301;
    store(key, 0);
    ASSERT_EQ(ctx_.gas_remaining, 2301);
    ASSERT_EQ(ctx_.gas_refund, 19900);
    ASSERT_EQ(load(key), 0);
}

TEST_F(RuntimeTest, StorageBerlinOriginalNonEmpty)
{
    using traits = EvmTraits<EVMC_BERLIN>;
    auto load = wrap(sload<traits>);
    auto store = wrap(sstore<traits>);

    // current == original
    auto &loc =
        host_.accounts[ctx_.env.recipient].storage[bytes32_from_uint256(key)];
    loc.original = bytes32_from_uint256(val);
    loc.current = bytes32_from_uint256(val);

    // nonempty -> same nonempty (cold)
    ctx_.gas_remaining = 2301;
    store(key, val);
    ASSERT_EQ(ctx_.gas_remaining, 201);
    ASSERT_EQ(load(key), val);

    // nonempty -> different nonempty (warm)
    ctx_.gas_remaining = 2800;
    store(key, val_2);
    ASSERT_EQ(ctx_.gas_remaining, 0);
    ASSERT_EQ(load(key), val_2);

    // nonempty -> empty (warm)
    ctx_.gas_remaining = 2301;
    store(key, 0);
    ASSERT_EQ(ctx_.gas_remaining, 2301);
    ASSERT_EQ(ctx_.gas_refund, 15000);
    ASSERT_EQ(load(key), 0);
}

TEST_F(RuntimeTest, StorageLondonOriginalNonEmpty)
{
    using traits = EvmTraits<EVMC_LONDON>;
    auto load = wrap(sload<traits>);
    auto store = wrap(sstore<traits>);

    // current == original
    auto &loc =
        host_.accounts[ctx_.env.recipient].storage[bytes32_from_uint256(key)];
    loc.original = bytes32_from_uint256(val);
    loc.current = bytes32_from_uint256(val);

    // nonempty -> same nonempty (cold)
    ctx_.gas_remaining = 2301;
    store(key, val);
    ASSERT_EQ(ctx_.gas_remaining, 201);
    ASSERT_EQ(load(key), val);

    // nonempty -> different nonempty (warm)
    ctx_.gas_remaining = 2800;
    store(key, val_2);
    ASSERT_EQ(ctx_.gas_remaining, 0);
    ASSERT_EQ(load(key), val_2);

    // nonempty -> empty (warm)
    ctx_.gas_remaining = 2301;
    store(key, 0);
    ASSERT_EQ(ctx_.gas_remaining, 2301);
    ASSERT_EQ(ctx_.gas_refund, 4800);
    ASSERT_EQ(load(key), 0);
}

TEST_F(RuntimeTest, StorageCancunLoadCold)
{
    using traits = EvmTraits<EVMC_CANCUN>;
    auto load = wrap(sload<traits>);

    ctx_.gas_remaining = 2000;
    ASSERT_EQ(load(key), 0);
    ASSERT_EQ(ctx_.gas_remaining, 0);
    ASSERT_EQ(load(key), 0);
    ASSERT_EQ(ctx_.gas_remaining, 0);
}

TEST_F(RuntimeTest, StorageCancunLoadWarm)
{
    using traits = EvmTraits<EVMC_CANCUN>;
    auto load = wrap(sload<traits>);

    host_.access_storage(ctx_.env.recipient, bytes32_from_uint256(key));

    ctx_.gas_remaining = 0;
    ASSERT_EQ(load(key), 0);
    ASSERT_EQ(ctx_.gas_remaining, 0);
}

TEST_F(RuntimeTest, StorageCancunOriginalEmpty)
{
    using traits = EvmTraits<EVMC_CANCUN>;
    auto load = wrap(sload<traits>);
    auto store = wrap(sstore<traits>);

    // empty -> nonempty (cold)
    ctx_.gas_remaining = 22000;
    store(key, val);
    ASSERT_EQ(ctx_.gas_remaining, 0);
    ASSERT_EQ(load(key), val);

    // nonempty -> nonempty (warm)
    ctx_.gas_remaining = 2301;
    store(key, val_2);
    ASSERT_EQ(ctx_.gas_remaining, 2301);
    ASSERT_EQ(load(key), val_2);

    // nonempty -> empty (warm)
    ctx_.gas_remaining = 2301;
    store(key, 0);
    ASSERT_EQ(ctx_.gas_remaining, 2301);
    ASSERT_EQ(ctx_.gas_refund, 19900);
    ASSERT_EQ(load(key), 0);
}

TEST_F(RuntimeTest, StorageCancunOriginalNonEmpty)
{
    using traits = EvmTraits<EVMC_CANCUN>;
    auto load = wrap(sload<traits>);
    auto store = wrap(sstore<traits>);

    // current == original
    auto &loc =
        host_.accounts[ctx_.env.recipient].storage[bytes32_from_uint256(key)];
    loc.original = bytes32_from_uint256(val);
    loc.current = bytes32_from_uint256(val);

    // nonempty -> same nonempty (cold)
    ctx_.gas_remaining = 2301;
    store(key, val);
    ASSERT_EQ(ctx_.gas_remaining, 201);
    ASSERT_EQ(load(key), val);

    // nonempty -> different nonempty (warm)
    ctx_.gas_remaining = 2800;
    store(key, val_2);
    ASSERT_EQ(ctx_.gas_remaining, 0);
    ASSERT_EQ(load(key), val_2);

    // nonempty -> empty (warm)
    ctx_.gas_remaining = 2301;
    store(key, 0);
    ASSERT_EQ(ctx_.gas_remaining, 2301);
    ASSERT_EQ(ctx_.gas_refund, 4800);
    ASSERT_EQ(load(key), 0);
}
