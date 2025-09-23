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

#include <category/core/assert.h>
#include <category/core/byte_string.hpp>
#include <category/core/config.hpp>
#include <category/execution/ethereum/core/block.hpp>
#include <category/execution/ethereum/core/rlp/block_rlp.hpp>
#include <category/execution/ethereum/db/block_db.hpp>

#include <brotli/decode.h>
#include <brotli/types.h>

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <filesystem>
#include <string>
#include <string_view>

MONAD_NAMESPACE_BEGIN

BlockDb::BlockDb(std::filesystem::path const &dir)
    : db_{dir.c_str()}
{
}

bool BlockDb::get(uint64_t const num, Block &block) const
{
    auto const key = std::to_string(num);
    auto result = db_.get(key.c_str());
    if (!result.has_value()) {
        auto const folder = std::to_string(num / 1000000) + 'M';
        auto const key = folder + '/' + std::to_string(num);
        result = db_.get(key.c_str());
    }
    if (!result.has_value()) {
        return false;
    }
    auto const view = to_byte_string_view(result.value());
    size_t brotli_size = std::max(result->size() * 100, 1ul << 20); // TODO
    byte_string brotli_buffer;
    brotli_buffer.resize(brotli_size);
    auto const brotli_result = BrotliDecoderDecompress(
        view.size(), view.data(), &brotli_size, brotli_buffer.data());
    brotli_buffer.resize(brotli_size);
    MONAD_ASSERT(brotli_result == BROTLI_DECODER_RESULT_SUCCESS);
    byte_string_view view2{brotli_buffer};

    auto const decoded_block = rlp::decode_block(view2);
    MONAD_ASSERT(!decoded_block.has_error());
    MONAD_ASSERT(view2.size() == 0);
    block = decoded_block.value();
    return true;
}

MONAD_NAMESPACE_END
