#include <category/core/assert.h>
#include <category/core/blake3.hpp>
#include <category/core/byte_string.hpp>
#include <category/core/bytes.hpp>
#include <category/execution/ethereum/core/fmt/bytes_fmt.hpp>
#include <category/execution/ethereum/wal_reader.hpp>
#include <category/execution/monad/core/rlp/monad_block_rlp.hpp>

#include <evmc/hex.hpp>

#include <sstream>

using std::ios;

MONAD_NAMESPACE_BEGIN

namespace
{

    constexpr auto WAL_ENTRY_SIZE =
        static_cast<std::streamoff>(sizeof(WalEntry));

    byte_string slurp_file(std::filesystem::path const &path)
    {
        MONAD_ASSERT(
            std::filesystem::exists(path) &&
            std::filesystem::is_regular_file(path));
        std::ifstream is(path);
        byte_string contents{
            std::istreambuf_iterator<char>(is),
            std::istreambuf_iterator<char>()};
        MONAD_ASSERT(is);
        return contents;
    }
}

WalReader::WalReader(
    MonadChain const &chain, std::filesystem::path const &ledger_dir)
    : chain_{chain}
    , ledger_dir_{ledger_dir}
{
    cursor_.open(ledger_dir_ / "wal", std::ios::binary);
    MONAD_ASSERT(cursor_);
}

std::optional<WalReader::Result> WalReader::next()
{
    WalEntry entry;
    auto const pos = cursor_.tellg();
    MONAD_ASSERT(pos != -1);
    if (MONAD_LIKELY(
            cursor_.read(reinterpret_cast<char *>(&entry), sizeof(WalEntry)))) {
        auto const header_filename = fmt::format(
            "{}.header", evmc::hex(to_byte_string_view(entry.id.bytes)));
        auto const header_data = slurp_file(ledger_dir_ / header_filename);
        byte_string_view header_view{header_data};
        auto const checksum_header = to_bytes(blake3(header_view));
        MONAD_ASSERT_PRINTF(
            checksum_header == entry.id,
            "Checksum failed for bft header %s",
            header_filename.c_str());
        auto const header_res =
            rlp::decode_consensus_block_header(chain_, header_view);
        MONAD_ASSERT_PRINTF(
            !header_res.has_error(),
            "Could not rlp decode file %s",
            header_filename.c_str());

        auto const body_filename =
            fmt::format("{}.body", evmc::hex(header_res.value().block_body_id));
        auto const body_data = slurp_file(ledger_dir_ / body_filename);
        auto const checksum_body = to_bytes(blake3(body_data));
        MONAD_ASSERT_PRINTF(
            checksum_body == header_res.value().block_body_id,
            "Checksum failed for bft block body %s",
            body_filename.c_str());
        byte_string_view body_view{body_data};
        auto const body_res = rlp::decode_consensus_block_body(body_view);
        MONAD_ASSERT_PRINTF(
            !header_res.has_error(),
            "Could not rlp decode file %s",
            body_filename.c_str());

        return Result{
            .action = entry.action,
            .header = std::move(header_res.value()),
            .body = std::move(body_res.value())};
    }
    else {
        // execution got ahead
        cursor_.clear();
        cursor_.seekg(pos);
        return {};
    }
}

bool WalReader::rewind_to(WalEntry const &rewind_entry)
{
    cursor_.seekg(0, ios::end);
    auto const size_on_start = cursor_.tellg();
    MONAD_ASSERT(size_on_start != -1);
    cursor_.seekg(0, ios::beg);

    if (size_on_start >= WAL_ENTRY_SIZE) {
        auto const pos =
            (size_on_start / WAL_ENTRY_SIZE) * WAL_ENTRY_SIZE - WAL_ENTRY_SIZE;
        cursor_.seekg(pos);
        while (cursor_) {
            WalEntry entry;
            if (!cursor_.read(
                    reinterpret_cast<char *>(&entry), sizeof(WalEntry))) {
                MONAD_ASSERT(false);
            }

            if (std::bit_cast<bytes32_t>(entry.id) ==
                    std::bit_cast<bytes32_t>(rewind_entry.id) &&
                entry.action == rewind_entry.action) {
                cursor_.seekg(-WAL_ENTRY_SIZE, ios::cur);

                return true;
            }

            cursor_.seekg(-2 * WAL_ENTRY_SIZE, ios::cur);
        }
    }
    cursor_.clear();
    cursor_.seekg(0, ios::beg);

    return false;
}

MONAD_NAMESPACE_END
