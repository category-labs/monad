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
#include <zkvm/test/corpus/spoke_code.hpp>

#include <category/core/assert.h>
#include <category/core/hex.hpp>

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
}

MONAD_NAMESPACE_END
