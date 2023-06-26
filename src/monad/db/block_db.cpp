#include <monad/core/assert.h>

#include <monad/db/block_db.hpp>

#include <monad/rlp/decode_helpers.hpp>

#include <brotli/decode.h>

#include <ethash/keccak.hpp>

MONAD_DB_NAMESPACE_BEGIN

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
    byte_string_view view2{brotli_buffer, brotli_size};

    auto const decoding_result = rlp::decode_block(block, view2);
    if (decoding_result.size() != 0) {
        return Status::DECODE_ERROR;
    }

    if (should_be_in_cache(num)) {
        store_current_block_hash(view2, num);
    }

    return Status::SUCCESS;
}

BlockDb::Status BlockDb::get_past_into_block_cache(block_num_t const num)
{
    // Read the child and use the parent hash from that block
    MONAD_DEBUG_ASSERT(num < current_block_);
    Block b{};
    auto const key = std::to_string(num + 1);
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
    byte_string_view view2{brotli_buffer, brotli_size};

    auto const decoding_result = rlp::decode_block(b, view2);
    if (decoding_result.size() != 0) {
        return Status::DECODE_ERROR;
    }

    recent_hashes_[write_index(num)] =
        std::bit_cast<bytes32_t>(b.header.parent_hash);

    return Status::SUCCESS;
}

bool BlockDb::should_be_in_cache(block_num_t n) const noexcept
{
    if (!current_block_) {
        return true;
    }
    if (n > current_block_.value()) {
        MONAD_DEBUG_ASSERT(is_next_block(n));
    }

    return is_next_block(n) ||
           ((earliest_block_in_cache() <= n) && (n <= current_block_.value()));
}

void BlockDb::store_current_block_hash(
    byte_string_view const v, block_num_t n) noexcept
{
    auto const h = rlp::get_rlp_header_from_block(v);

    recent_hashes_[write_index(n)] =
        std::bit_cast<bytes32_t>(ethash::keccak256(h.data(), h.size()));
    current_block_ =
        current_block_
            ? (n > current_block_.value()) ? n : current_block_.value()
            : n;
}

[[nodiscard]] bytes32_t BlockDb::get_block_hash(block_num_t number)
{
    if (should_be_in_cache(number)) {
        if (recent_hashes_[write_index(number)] == null) {
            auto const status = get_past_into_block_cache(number);
            MONAD_DEBUG_ASSERT(status == Status::SUCCESS);
        }
        return recent_hashes_[write_index(number)];
    }
    // YP Appendix H.2, 40s BLOCKHASH, 1st condition
    return bytes32_t{};
}

MONAD_DB_NAMESPACE_END
