#include <monad/db/block_db.hpp>

#include <silkworm/common/assert.hpp>
#include <silkworm/common/decoding_result.hpp>

#include <brotli/decode.h>
#include <brotli/encode.h>

#include <cstdint>
#include <string>

MONAD_NAMESPACE_BEGIN

BlockDb::BlockDb(std::filesystem::path const &dir)
    : db_{dir.c_str()}
{
}

bool BlockDb::get(silkworm::BlockNum const num, silkworm::Block &block) const
{
    auto const key = std::to_string(num);
    auto const result = db_.get(key.c_str());
    if (!result.has_value()) {
        return false;
    }
    silkworm::ByteView view{
        reinterpret_cast<uint8_t const *>(result->data()), result->length()};
    size_t brotli_size = result->size() * 100; // TODO
    silkworm::Bytes brotli_buffer;
    brotli_buffer.resize(brotli_size);
    auto const brotli_result = BrotliDecoderDecompress(
        view.size(), view.data(), &brotli_size, brotli_buffer.data());
    brotli_buffer.resize(brotli_size);
    SILKWORM_ASSERT(brotli_result == BROTLI_DECODER_RESULT_SUCCESS);
    silkworm::ByteView view2{brotli_buffer};
    auto const decoding_result = silkworm::rlp::decode(view2, block);
    SILKWORM_ASSERT(decoding_result == silkworm::DecodingResult::kOk);
    return true;
}

void BlockDb::upsert(
    silkworm::BlockNum const num, silkworm::Block const &block) const
{
    auto const key = std::to_string(num);
    silkworm::Bytes bytes;
    silkworm::rlp::encode(bytes, block);
    size_t brotli_size = BrotliEncoderMaxCompressedSize(bytes.size());
    SILKWORM_ASSERT(brotli_size);
    silkworm::Bytes brotli_buffer;
    brotli_buffer.resize(brotli_size);
    auto const brotli_result = BrotliEncoderCompress(
        BROTLI_DEFAULT_QUALITY,
        BROTLI_DEFAULT_WINDOW,
        BROTLI_MODE_GENERIC,
        bytes.size(),
        bytes.data(),
        &brotli_size,
        brotli_buffer.data());
    SILKWORM_ASSERT(brotli_result == BROTLI_TRUE);
    brotli_buffer.resize(brotli_size);
    std::string_view const value{
        reinterpret_cast<char const *>(brotli_buffer.data()),
        brotli_buffer.size()};
    db_.upsert(key.c_str(), value);
}

void BlockDb::remove(silkworm::BlockNum const num) const
{
    auto const key = std::to_string(num);
    db_.remove(key.c_str());
}

MONAD_NAMESPACE_END
