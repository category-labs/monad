#include <monad/core/assert.h>

#include <monad/db/block_db.hpp>

#include <monad/rlp/decode_helpers.hpp>

#include <brotli/decode.h>

#include <ethash/keccak.hpp>

MONAD_NAMESPACE_BEGIN

BlockDb::Status BlockDb::get(block_num_t const num, Block &block)
{
    auto const key = std::to_string(num);
    auto const result = db_.get(key.c_str());
    if (!result.has_value()) {
        return Status::NO_BLOCK_FOUND;
    }
    byte_string_view view{
        reinterpret_cast<uint8_t const *>(result->data()), result->length()};

    size_t brotli_size = 1'048'576u; // 1M

    uint8_t brotli_buffer[1'048'567u];

    auto brotli_result = BrotliDecoderDecompress(
        view.length(), view.data(), &brotli_size, brotli_buffer);

    if (brotli_result != BROTLI_DECODER_RESULT_SUCCESS) {
        return Status::DECOMPRESS_ERROR;
    }

    auto const decoding_result =
        rlp::decode_block(block, {brotli_buffer, brotli_size});
    if (decoding_result.size() != 0) {
        return Status::DECODE_ERROR;
    }

    return Status::SUCCESS;
}

MONAD_NAMESPACE_END
