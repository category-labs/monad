#include <monad/core/assert.h>
#include <monad/db/block_db.hpp>
#include <monad/rlp/decode_helpers.hpp>
#include <monad/rlp/encode_helpers.hpp>

#include <brotli/decode.h>
#include <brotli/encode.h>

#include <cstdint>
#include <string>

MONAD_DB_NAMESPACE_BEGIN

// TODO: test for this function?
bool BlockDb::get(block_num_t const num, Block &block) const
{
    auto const key = std::to_string(num);
    auto const result = db_.get(key.c_str());
    if (!result.has_value()) {
        return false;
    }
    byte_string_view view{
        reinterpret_cast<uint8_t const *>(result->data()), result->length()};

    auto compression_factor = 100u;
    auto brotli_result = BrotliDecoderResult::BROTLI_DECODER_RESULT_ERROR;
    byte_string brotli_buffer;
    size_t brotli_size = 0u;

    while (brotli_result != BROTLI_DECODER_RESULT_SUCCESS) {
        brotli_size = result->size() * compression_factor;
        brotli_buffer.resize(brotli_size);
        brotli_result = BrotliDecoderDecompress(
            view.size(), view.data(), &brotli_size, brotli_buffer.data());
        compression_factor *= 10u;
    }

    brotli_buffer.resize(brotli_size);
    MONAD_ASSERT(brotli_result == BROTLI_DECODER_RESULT_SUCCESS);
    byte_string_view view2{brotli_buffer};

    auto const decoding_result = rlp::decode_block(block, view2);
    MONAD_ASSERT(decoding_result.size() == 0);
    return true;
}

MONAD_DB_NAMESPACE_END