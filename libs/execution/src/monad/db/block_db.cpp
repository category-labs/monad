#include <monad/config.hpp>
#include <monad/core/assert.h>
#include <monad/core/block.hpp>
#include <monad/core/byte_string.hpp>
#include <monad/core/rlp/block_rlp.hpp>
#include <monad/db/block_db.hpp>

#include <brotli/decode.h>
#include <brotli/encode.h>
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

    BrotliDecoderState *state =
        BrotliDecoderCreateInstance(nullptr, nullptr, nullptr);
    MONAD_ASSERT(state != nullptr);

    uint8_t const *next_in = view.data();
    size_t available_in = view.size();

    size_t const buffer_size = 1 << 16; // TODO: bench for optimal size
    std::vector<uint8_t> buffer(buffer_size);
    uint8_t *next_out = buffer.data();
    size_t available_out = buffer.size();
    size_t total_out = 0;

    std::vector<uint8_t> decompressed;
    decompressed.reserve(
        std::min(view.size() * 4, buffer_size)); // TODO: bench for optimal size

    while (true) {
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

        size_t const out_size = buffer_size - available_out;
        decompressed.insert(
            decompressed.end(), buffer.data(), buffer.data() + out_size);

        if (result == BROTLI_DECODER_RESULT_SUCCESS) {
            break;
        }

        next_out = buffer.data();
        available_out = buffer.size();
    }

    BrotliDecoderDestroyInstance(state);
    byte_string_view view2{decompressed};
    auto const decoded_block = rlp::decode_block(view2);
    MONAD_ASSERT(!decoded_block.has_error());
    MONAD_ASSERT(view2.size() == 0);
    block = decoded_block.value();
    return true;
}

void BlockDb::upsert(uint64_t const num, Block const &block) const
{
    auto const key = std::to_string(num);
    auto const encoded_block = rlp::encode_block(block);
    size_t brotli_size = BrotliEncoderMaxCompressedSize(encoded_block.size());
    MONAD_ASSERT(brotli_size);
    byte_string brotli_buffer;
    brotli_buffer.resize(brotli_size);
    auto const brotli_result = BrotliEncoderCompress(
        BROTLI_DEFAULT_QUALITY,
        BROTLI_DEFAULT_WINDOW,
        BROTLI_MODE_GENERIC,
        encoded_block.size(),
        encoded_block.data(),
        &brotli_size,
        brotli_buffer.data());
    MONAD_ASSERT(brotli_result == BROTLI_TRUE);
    brotli_buffer.resize(brotli_size);
    std::string_view const value{
        reinterpret_cast<char const *>(brotli_buffer.data()),
        brotli_buffer.size()};
    db_.upsert(key.c_str(), value);
}

bool BlockDb::remove(uint64_t const num) const
{
    auto const key = std::to_string(num);
    return db_.remove(key.c_str());
}

MONAD_NAMESPACE_END
