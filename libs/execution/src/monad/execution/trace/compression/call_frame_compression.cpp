#include <monad/core/assert.h>
#include <monad/core/byte_string.hpp>
#include <monad/execution/trace/call_frame.hpp>
#include <monad/execution/trace/compression/call_frame_compression.hpp>
#include <monad/execution/trace/rlp/call_frame_rlp.hpp>
#include <monad/rlp/config.hpp>

#include <brotli/decode.h>
#include <brotli/encode.h>
#include <brotli/types.h>

#include <span>
#include <vector>

MONAD_NAMESPACE_BEGIN

byte_string compress_call_frames(byte_string_view const rlp_call_frames)
{
    size_t brotli_size_required =
        BrotliEncoderMaxCompressedSize(rlp_call_frames.length());
    MONAD_ASSERT(brotli_size_required);

    thread_local std::unique_ptr<uint8_t[]> brotli_buffer;
    thread_local size_t brotli_buffer_capacity = 0;

    if (MONAD_UNLIKELY(brotli_buffer_capacity < brotli_size_required)) {
        brotli_buffer.reset(new uint8_t[brotli_size_required]);
        brotli_buffer_capacity = brotli_size_required;
    }

    size_t brotli_size_compressed = brotli_size_required;

    auto const brotli_result = BrotliEncoderCompress(
        1,
        BROTLI_DEFAULT_WINDOW,
        BROTLI_MODE_GENERIC,
        rlp_call_frames.size(),
        rlp_call_frames.data(),
        &brotli_size_compressed,
        brotli_buffer.get());
    MONAD_ASSERT(brotli_result == BROTLI_TRUE);

    return byte_string(
        brotli_buffer.get(), brotli_buffer.get() + brotli_size_compressed);
}

byte_string
decompress_call_frames(byte_string_view const compressed_call_frames)
{
    // DBTest.call_frames_stress_test compression factor is between 1000 and 10000
    size_t const max_compression_factor = 10000;
    size_t brotli_size =
        compressed_call_frames.length() * max_compression_factor;
    byte_string brotli_buffer;
    brotli_buffer.resize(brotli_size);

    auto const brotli_result = BrotliDecoderDecompress(
        compressed_call_frames.length(),
        compressed_call_frames.data(),
        &brotli_size,
        brotli_buffer.data());
    MONAD_ASSERT(brotli_result == BROTLI_DECODER_RESULT_SUCCESS);
    brotli_buffer.resize(brotli_size);

    return brotli_buffer;
}

MONAD_NAMESPACE_END
