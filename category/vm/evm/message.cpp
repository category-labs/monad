// Copyright (C) 2025-26 Category Labs, Inc.
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

#include <category/vm/evm/message.hpp>

#include <evmc/evmc.h>

#include <bit>
#include <cstddef>
#include <type_traits>
#include <utility>

// Value equality with evmc_call_kind / evmc_flags.
static_assert(sizeof(monad_call_kind) == sizeof(evmc_call_kind));

#define MONAD_ASSERT_ENUM_EQ(name)                                             \
    static_assert(                                                             \
        std::to_underlying(MONAD_##name) == std::to_underlying(EVMC_##name))

MONAD_ASSERT_ENUM_EQ(CALL);
MONAD_ASSERT_ENUM_EQ(DELEGATECALL);
MONAD_ASSERT_ENUM_EQ(CALLCODE);
MONAD_ASSERT_ENUM_EQ(CREATE);
MONAD_ASSERT_ENUM_EQ(CREATE2);
MONAD_ASSERT_ENUM_EQ(EOFCREATE);
MONAD_ASSERT_ENUM_EQ(STATIC);
MONAD_ASSERT_ENUM_EQ(DELEGATED);

#undef MONAD_ASSERT_ENUM_EQ

// Layout equality with evmc_message; the bit_casts below rely on it.
static_assert(std::is_standard_layout_v<monad_message>);
static_assert(std::is_trivially_copyable_v<monad_message>);
static_assert(sizeof(monad_message) == 192);
static_assert(sizeof(monad_message) == sizeof(evmc_message));
static_assert(alignof(monad_message) == alignof(evmc_message));

#define MONAD_ASSERT_MESSAGE_FIELD_EQ(field)                                   \
    static_assert(                                                             \
        offsetof(monad_message, field) == offsetof(evmc_message, field))

MONAD_ASSERT_MESSAGE_FIELD_EQ(kind);
MONAD_ASSERT_MESSAGE_FIELD_EQ(flags);
MONAD_ASSERT_MESSAGE_FIELD_EQ(depth);
MONAD_ASSERT_MESSAGE_FIELD_EQ(gas);
MONAD_ASSERT_MESSAGE_FIELD_EQ(recipient);
MONAD_ASSERT_MESSAGE_FIELD_EQ(sender);
MONAD_ASSERT_MESSAGE_FIELD_EQ(input_data);
MONAD_ASSERT_MESSAGE_FIELD_EQ(input_size);
MONAD_ASSERT_MESSAGE_FIELD_EQ(value);
MONAD_ASSERT_MESSAGE_FIELD_EQ(create2_salt);
MONAD_ASSERT_MESSAGE_FIELD_EQ(code_address);
MONAD_ASSERT_MESSAGE_FIELD_EQ(memory_handle);
MONAD_ASSERT_MESSAGE_FIELD_EQ(memory);
MONAD_ASSERT_MESSAGE_FIELD_EQ(memory_capacity);

#undef MONAD_ASSERT_MESSAGE_FIELD_EQ

// Same offset does not rule out a narrowed field padded back to the next one;
// the enum is pinned above, Address/bytes32_t in their own headers.
#define MONAD_ASSERT_MESSAGE_FIELD_TYPE_EQ(field)                              \
    static_assert(std::is_same_v<                                              \
                  decltype(monad_message::field),                              \
                  decltype(evmc_message::field)>)

MONAD_ASSERT_MESSAGE_FIELD_TYPE_EQ(flags);
MONAD_ASSERT_MESSAGE_FIELD_TYPE_EQ(depth);
MONAD_ASSERT_MESSAGE_FIELD_TYPE_EQ(gas);
MONAD_ASSERT_MESSAGE_FIELD_TYPE_EQ(input_data);
MONAD_ASSERT_MESSAGE_FIELD_TYPE_EQ(input_size);
MONAD_ASSERT_MESSAGE_FIELD_TYPE_EQ(memory_handle);
MONAD_ASSERT_MESSAGE_FIELD_TYPE_EQ(memory);
MONAD_ASSERT_MESSAGE_FIELD_TYPE_EQ(memory_capacity);

#undef MONAD_ASSERT_MESSAGE_FIELD_TYPE_EQ

evmc_message to_evmc_message(monad_message const &msg)
{
    return std::bit_cast<evmc_message>(msg);
}

monad_message from_evmc_message(evmc_message const &msg)
{
    return std::bit_cast<monad_message>(msg);
}
