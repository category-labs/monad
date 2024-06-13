#include <monad/config.hpp>
#include <monad/core/assert.h>
#include <monad/core/block.hpp>
#include <monad/core/byte_string.hpp>
#include <monad/core/rlp/block_rlp.hpp>
#include <monad/db/block_db.hpp>

#include <brotli/decode.h>
#include <brotli/encode.h>
#include <brotli/types.h>
#include <quill/Quill.h>

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <filesystem>
#include <string>
#include <string_view>

using namespace monad;

static bool
brotli_decompress_block_view(
        byte_string &brotli_buffer, byte_string_view const &view)
{
    size_t brotli_size = 0;
    size_t available_in = view.size();
    size_t available_out = available_in * 5;
    brotli_buffer.resize(available_out);
    BrotliDecoderResult brotli_result;
    std::unique_ptr< BrotliDecoderState,
        void (*)(BrotliDecoderState *)> brotli_state{
            BrotliDecoderCreateInstance(nullptr, nullptr, nullptr),
            BrotliDecoderDestroyInstance};
    uint8_t const *next_in = view.data();
    do {
        uint8_t *next_out = &brotli_buffer.data()[brotli_size];
        brotli_result = BrotliDecoderDecompressStream(
            brotli_state.get(),
            &available_in,
            &next_in,
            &available_out,
            &next_out,
            &brotli_size);
        if (brotli_result != BROTLI_DECODER_RESULT_NEEDS_MORE_OUTPUT) {
            break;
        }
        // Need more decompressed data. Allocate buffer space for it:
        available_out += brotli_buffer.size();
        brotli_buffer.resize(2 * brotli_buffer.size());
    } while (true);
    brotli_buffer.resize(brotli_size);
    return brotli_result == BROTLI_DECODER_RESULT_SUCCESS;
}

MONAD_NAMESPACE_BEGIN

BlockDb::BlockDb(
        std::filesystem::path const &dir, BlockCompression compression)
    : db_{dir.c_str()}, compression_{compression}
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
    byte_string decompress_buffer;
    auto view = to_byte_string_view(result.value());
    if (compression_ == BlockCompression::Brotli) {
        if (!brotli_decompress_block_view(decompress_buffer, view)) {
            LOG_INFO("Block decompression failed");
            return false;
        }
        view = decompress_buffer;
    }
    auto const decoded_block = rlp::decode_block(view);
    if (decoded_block.has_error()) {
        LOG_INFO("block decoding failed");
        return false;
    }
    MONAD_ASSERT(view.size() == 0);
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
