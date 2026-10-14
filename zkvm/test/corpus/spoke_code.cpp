// Copyright (C) 2026 Category Labs, Inc.
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

#include <zkvm/test/corpus/contracts/namespace_spoke_runtime.hpp>
#include <zkvm/test/corpus/genesis_bulk.hpp>
#include <zkvm/test/corpus/spoke_code.hpp>

#include <category/core/assert.h>
#include <category/core/hex.hpp>
#include <category/execution/ethereum/core/account.hpp>
#include <category/execution/ethereum/domain_anchor.hpp>
#include <category/execution/ethereum/state3/state.hpp>

#include <cstring>
#include <utility>

MONAD_NAMESPACE_BEGIN

namespace corpus
{
    byte_string
    namespace_spoke_code(uint64_t const namespace_chain_id, Address const &op)
    {
        auto code = from_hex(NAMESPACE_SPOKE_RUNTIME_HEX);
        MONAD_ASSERT(code.has_value());
        byte_string out = std::move(code).value();
        // Each immutable is a 32-byte word, as the constructor stores it: the
        // chain id big-endian, the operator right-aligned.
        for (std::size_t const at : NAMESPACE_SPOKE_CHAIN_ID_AT) {
            MONAD_ASSERT(at + 32 <= out.size());
            for (unsigned i = 0; i < 8; ++i) {
                out[at + 24 + i] = static_cast<unsigned char>(
                    namespace_chain_id >> (56 - 8 * i));
            }
        }
        for (std::size_t const at : NAMESPACE_SPOKE_OPERATOR_AT) {
            MONAD_ASSERT(at + 32 <= out.size());
            std::memcpy(out.data() + at + 12, op.bytes, sizeof(op.bytes));
        }
        return out;
    }

    byte_string spoke_access_proxy(Address const &impl)
    {
        // sel = calldataload(0) >> 224; if (sel == canCall) goto allow;
        //   calldatacopy(0, 0, calldatasize())
        //   ok = delegatecall(gas, impl, 0, calldatasize(), 0, 0)
        //   returndatacopy(0, 0, returndatasize())
        //   if (ok) return(0, returndatasize()) else revert(0,
        //   returndatasize())
        // allow: mstore(0, 1); return(0, 32)
        //
        // The two jump destinations are absolute, so the layout below is the
        // code: 0x40 is the success JUMPDEST and 0x45 the allow one. Spelled
        // out byte for byte because a hand-written offset is exactly what
        // drifts when the body changes.
        byte_string out{
            0x60, 0x00, // 0x00 PUSH1 0
            0x35, // 0x02 CALLDATALOAD
            0x60, 0xe0, // 0x03 PUSH1 224
            0x1c, // 0x05 SHR
            0x63, 0xf0, 0xf9, 0x67, 0xe8, // 0x06 PUSH4 canCall selector
            0x14, // 0x0b EQ
            0x60, 0x45, // 0x0c PUSH1 allow
            0x57, // 0x0e JUMPI
            0x36, // 0x0f CALLDATASIZE
            0x60, 0x00, // 0x10 PUSH1 0
            0x60, 0x00, // 0x12 PUSH1 0
            0x37, // 0x14 CALLDATACOPY
            0x60, 0x00, // 0x15 PUSH1 0   retSize
            0x60, 0x00, // 0x17 PUSH1 0   retOffset
            0x36, // 0x19 CALLDATASIZE argsSize
            0x60, 0x00, // 0x1a PUSH1 0   argsOffset
            0x73, // 0x1c PUSH20 impl
        };
        out.append(impl.bytes, sizeof(impl.bytes));
        byte_string const tail{
            0x5a, // 0x31 GAS
            0xf4, // 0x32 DELEGATECALL
            0x3d, // 0x33 RETURNDATASIZE
            0x60, 0x00, // 0x34 PUSH1 0
            0x60, 0x00, // 0x36 PUSH1 0
            0x3e, // 0x38 RETURNDATACOPY
            0x60, 0x40, // 0x39 PUSH1 ok
            0x57, // 0x3b JUMPI
            0x3d, // 0x3c RETURNDATASIZE
            0x60, 0x00, // 0x3d PUSH1 0
            0xfd, // 0x3f REVERT
            0x5b, // 0x40 JUMPDEST (ok)
            0x3d, // 0x41 RETURNDATASIZE
            0x60, 0x00, // 0x42 PUSH1 0
            0xf3, // 0x44 RETURN
            0x5b, // 0x45 JUMPDEST (allow)
            0x60, 0x01, // 0x46 PUSH1 1
            0x60, 0x00, // 0x48 PUSH1 0
            0x52, // 0x4a MSTORE
            0x60, 0x20, // 0x4b PUSH1 32
            0x60, 0x00, // 0x4d PUSH1 0
            0xf3, // 0x4f RETURN
        };
        out += tail;
        MONAD_ASSERT(out.size() == 0x50);
        MONAD_ASSERT(out[0x40] == 0x5b && out[0x45] == 0x5b);
        return out;
    }

    void seed_spoke_access(State &state)
    {
#ifdef MONAD_ZKVM_L2
        state.create_contract(L2_DOMAIN_SPOKE);
        state.set_code(
            L2_DOMAIN_SPOKE, spoke_access_proxy(SPOKE_IMPLEMENTATION));
#else
        (void)state;
#endif
    }

    void seed_spoke_access(GenesisSink &sink)
    {
#ifdef MONAD_ZKVM_L2
        sink.contract(
            L2_DOMAIN_SPOKE,
            Account{},
            spoke_access_proxy(SPOKE_IMPLEMENTATION));
#else
        (void)sink;
#endif
    }
}

MONAD_NAMESPACE_END
