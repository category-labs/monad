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

#pragma once

#include <category/core/byte_string.hpp>
#include <category/core/bytes.hpp>
#include <category/core/config.hpp>
#include <category/execution/ethereum/core/address.hpp>
#include <category/execution/ethereum/core/receipt.hpp>

MONAD_NAMESPACE_BEGIN

// Simple API for building events in a solidity compatible manner. Data should
// be encoded using the abi helpers.
class EventBuilder
{
    Receipt::Log event_;

public:
    explicit EventBuilder(Address const &account, bytes32_t const &signature)
    {
        event_.address = account;
        event_.topics.push_back(signature);
    }

    // Add an indexed parameter
    EventBuilder &&add_topic(bytes32_t const &topic) &&
    {
        event_.topics.push_back(topic);
        return std::move(*this);
    }

    // Add a non-indexed parameter
    EventBuilder &&add_data(byte_string_view const data) &&
    {
        event_.data += data;
        return std::move(*this);
    }

    // noinline is here for gcc only. The optimizer inlines this method, and
    // then errors out because the call to memmove appears to exceed the size of
    // the object. Once inlined, it doesn't realize the Receipt::Log object has
    // a byte_string, which has an SSO buffer. Blocking inlining gives gcc
    // enough context to realize this move is perfectly safe.
    [[gnu::noinline]] Receipt::Log &&build() &&
    {
        return std::move(event_);
    }
};

MONAD_NAMESPACE_END
