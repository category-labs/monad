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

#include <category/mpt/compute.hpp>
#include <category/mpt/config.hpp>

#include <span>

MONAD_MPT_NAMESPACE_BEGIN

std::span<unsigned char> encode_empty_string(std::span<unsigned char> result)
{
    result[0] = RLP_EMPTY_STRING;
    return result.subspan(1);
}

std::span<unsigned char> encode_16_children(
    std::span<ChildData> const children, std::span<unsigned char> result)
{
    unsigned i = 0;
    for (auto &child : children) {
        if (child.is_valid()) {
            MONAD_DEBUG_ASSERT(child.branch < 16);
            while (child.branch != i) {
                result[0] = RLP_EMPTY_STRING;
                result = result.subspan(1);
                ++i;
            }
            MONAD_DEBUG_ASSERT(i == child.branch);
            result = (child.len < KECCAK256_SIZE)
                         ? [&] {
                               memcpy(result.data(), child.data, child.len);
                               return result.subspan(child.len);
                           }()
                         : rlp::encode_string(result, {child.data, child.len});
            ++i;
        }
    }
    // encode empty value string
    for (; i < 16; ++i) {
        result = encode_empty_string(result);
    }
    return result;
}

std::span<unsigned char>
encode_16_children(Node const &node, std::span<unsigned char> result)
{

    for (unsigned i = 0, bit = 1; i < 16; ++i, bit <<= 1) {
        if (node.mask & bit) {
            auto const child_index = node.to_child_index(i);
            MONAD_DEBUG_ASSERT(
                node.child_data_len(child_index) <= KECCAK256_SIZE);
            result =
                (node.child_data_len(child_index) < KECCAK256_SIZE)
                    ? [&] {
                          memcpy(
                              result.data(),
                              node.child_data(child_index),
                              node.child_data_len(child_index));
                          return result.subspan(
                              node.child_data_len(child_index));
                      }()
                    : rlp::encode_string(result, node.child_data_view(child_index));
        }
        else {
            result = encode_empty_string(result);
        }
    }
    return result;
}

MONAD_MPT_NAMESPACE_END
