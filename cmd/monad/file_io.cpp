#include "file_io.hpp"

#include <category/core/assert.h>
#include <category/core/blake3.hpp>
#include <category/execution/ethereum/core/fmt/bytes_fmt.hpp>
#include <category/execution/monad/core/rlp/monad_block_rlp.hpp>

#include <evmc/evmc.hpp>

#include <fstream>
#include <sstream>

MONAD_NAMESPACE_BEGIN

byte_string read_file(bytes32_t const &id, std::filesystem::path const &dir)
{
    auto const filename = evmc::hex(id);
    auto const path = dir / filename;
    MONAD_ASSERT(
        std::filesystem::exists(path) &&
        std::filesystem::is_regular_file(path));
    std::ifstream is(path);
    MONAD_ASSERT(is);
    byte_string const data{
        std::istreambuf_iterator<char>(is), std::istreambuf_iterator<char>()};
    auto const checksum = to_bytes(blake3(data));
    MONAD_ASSERT_PRINTF(
        checksum == id, "Checksum failed for bft header: %s", filename.c_str());
    return data;
}

MonadConsensusBlockBody
read_body(bytes32_t const &id, std::filesystem::path const &dir)
{
    auto const data = read_file(id, dir);
    byte_string_view view{data};
    auto const res = rlp::decode_consensus_block_body(view);
    MONAD_ASSERT_PRINTF(
        !res.has_error(),
        "Could not rlp decode body: %s",
        evmc::hex(id).c_str());
    return res.value();
}

bytes32_t head_pointer_to_id(std::filesystem::path const &symlink)
{
    char resolved[PATH_MAX] = {};
    auto const r = readlink(symlink.c_str(), resolved, sizeof(resolved));
    if (MONAD_UNLIKELY(r == -1)) {
        return bytes32_t{};
    }

    auto const id_string = std::filesystem::path(resolved).stem().string();
    auto const decode_res = evmc::from_hex(id_string);
    MONAD_ASSERT_PRINTF(
        decode_res.has_value(),
        "Link not hex encoded %s -> %s",
        symlink.c_str(),
        resolved);
    byte_string const hex = decode_res.value();
    return to_bytes(hex);
}

MONAD_NAMESPACE_END
