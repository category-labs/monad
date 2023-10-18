#pragma once

#include <monad/config.hpp>
#include <monad/core/block.hpp>
#include <monad/core/bytes.hpp>

#include <monad/db/file_db.hpp>

#include <array>
#include <filesystem>

MONAD_NAMESPACE_BEGIN

class BlockDb
{
public:
    BlockDb(std::filesystem::path const &block_db_path)
        : db_{block_db_path.c_str()} {};
    ~BlockDb() = default;

    enum class Status
    {
        SUCCESS,
        NO_BLOCK_FOUND,
        DECOMPRESS_ERROR,
        DECODE_ERROR
    };

    static constexpr auto null{
        0x0000000000000000000000000000000000000000000000000000000000000000_bytes32};

    [[nodiscard]] Status get(block_num_t, Block &);
    // Support BLOCKHASH opcode, See YP Sec. 12.2
    [[nodiscard]] bytes32_t get_block_hash(block_num_t);

    void store_current_block_hash(block_num_t) noexcept;
    [[nodiscard]] Status get_past_into_block_cache(block_num_t);
    [[nodiscard]] bool should_be_in_cache(block_num_t) const noexcept;

    [[nodiscard]] bool is_next_block(block_num_t n) const noexcept
    {
        return n == (current_block_.value() + 1);
    }

    [[nodiscard]] block_num_t earliest_block_in_cache() const noexcept
    {
        return ((current_block_.value() - number_of_hashes) >
                current_block_.value())
                   ? 0u
                   : (current_block_.value() - number_of_hashes);
    }

    [[nodiscard]] size_t write_index(block_num_t n) const noexcept
    {
        return n % number_of_hashes;
    }

    // YP Appendix H.2, 40s BLOCKHASH
    static constexpr auto number_of_hashes{256u};

private:
    FileDb db_;
    std::array<bytes32_t, number_of_hashes> recent_hashes_{};
    std::optional<block_num_t> current_block_{};
    byte_string current_block_decoded_;
};

MONAD_NAMESPACE_END
