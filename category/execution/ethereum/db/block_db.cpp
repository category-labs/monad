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

    BrotliDecoderState *const state =
        BrotliDecoderCreateInstance(nullptr, nullptr, nullptr);
    MONAD_ASSERT(state != nullptr);

    constexpr size_t INC_SIZE = 1ul << 20;

    uint8_t const *next_in = view.data();
    size_t available_in = view.size();

    byte_string out{};
    size_t available_out = INC_SIZE;
    out.resize_and_overwrite(
        available_out, [](auto *, size_t const count) { return count; });
    size_t total_out = 0;

    while (true) {
        uint8_t *next_out = out.data() + total_out;
        auto const result = BrotliDecoderDecompressStream(
            state,
            &available_in,
            &next_in,
            &available_out,
            &next_out,
            &total_out);

        MONAD_ASSERT(
            (result != BROTLI_DECODER_RESULT_ERROR) &&
            (result != BROTLI_DECODER_RESULT_NEEDS_MORE_INPUT));

        if (result == BROTLI_DECODER_RESULT_SUCCESS) {
            break;
        }

        if (result == BROTLI_DECODER_RESULT_NEEDS_MORE_OUTPUT) {
            out.resize_and_overwrite(
                out.size() + INC_SIZE,
                [](auto *, size_t const count) { return count; });
            available_out += INC_SIZE;
        }
    }
    out.resize(total_out);

    BrotliDecoderDestroyInstance(state);
    byte_string_view out_view{out};
    auto const decoded_block = rlp::decode_block(out_view);
    MONAD_ASSERT(!decoded_block.has_error());
    MONAD_ASSERT(out_view.size() == 0);
    block = decoded_block.value();
    return true;
}

MONAD_NAMESPACE_END
