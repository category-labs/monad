// Copyright (C) 2025 Category Labs, Inc.
//
// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with this program.  If not, see <http://www.gnu.org/licenses/>.

#include "wal.hpp"
#include "file_io.hpp"

#include <category/core/assert.h>
#include <category/core/blake3.hpp>
#include <category/core/byte_string.hpp>
#include <category/core/bytes.hpp>
#include <category/core/config.hpp>
#include <category/execution/ethereum/core/fmt/bytes_fmt.hpp>
#include <category/execution/monad/chain/monad_chain.hpp>
#include <category/execution/monad/core/rlp/monad_block_rlp.hpp>

#include <evmc/hex.hpp>

#include <filesystem>
#include <sstream>
#include <tuple>

using std::ios;

MONAD_ANONYMOUS_NAMESPACE_BEGIN

template <class MonadConsensusBlockHeader>
std::pair<MonadConsensusBlockHeader, bytes32_t>
decode_block_header(bytes32_t const &id, byte_string_view data)
{
    auto h =
        rlp::decode_consensus_block_header<MonadConsensusBlockHeader>(data);
    MONAD_ASSERT_PRINTF(
        !h.has_error(),
        "Could not rlp decode header: %s",
        evmc::hex(id).c_str());
    bytes32_t block_body_id = h.value().block_body_id;
    return std::make_pair(std::move(h.value()), std::move(block_body_id));
}

MONAD_ANONYMOUS_NAMESPACE_END

MONAD_NAMESPACE_BEGIN

WalReader::WalReader(
    MonadChain const &chain, std::filesystem::path const &ledger_dir)
    : chain_{chain}
    , ledger_dir_{ledger_dir}
    , header_dir_{ledger_dir / "headers"}
    , bodies_dir_{ledger_dir / "bodies"}
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
        std::variant<
            MonadConsensusBlockHeaderV0,
            MonadConsensusBlockHeaderV1,
            MonadConsensusBlockHeaderV2>
            header;
        bytes32_t bft_body_id;
        auto const data = read_file(entry.id, header_dir_);
        byte_string_view view{data};
        auto const ts = rlp::decode_consensus_block_header_timestamp_s(view);
        MONAD_ASSERT_PRINTF(
            !ts.has_error(),
            "Could not rlp decode timestamp from header: %s",
            evmc::hex(entry.id).c_str());
        auto const monad_rev = chain_.get_monad_revision(ts.value());
        if (monad_rev >= MONAD_FOUR) {
            std::tie(header, bft_body_id) =
                decode_block_header<MonadConsensusBlockHeaderV2>(
                    entry.id, data);
        }
        else if (monad_rev == MONAD_THREE) {
            std::tie(header, bft_body_id) =
                decode_block_header<MonadConsensusBlockHeaderV1>(
                    entry.id, data);
        }
        else {
            std::tie(header, bft_body_id) =
                decode_block_header<MonadConsensusBlockHeaderV0>(
                    entry.id, data);
        }

        return Result{
            .action = entry.action,
            .block_id = entry.id,
            .header = std::move(header),
            .body = read_body(bft_body_id, bodies_dir_)};
    }
    else {
        // execution got ahead
        cursor_.clear();
        cursor_.seekg(pos);
        return {};
    }
}

WalWriter::WalWriter(std::filesystem::path const &ledger_dir)
    : wal_path_{ledger_dir / "wal"}
{
}

void WalWriter::write(WalAction action, bytes32_t const &block_id)
{
    if (!cursor_.is_open()) {
        // Opening of the file is deferred to the first write, to give
        // consensus time to create wal_path_
        cursor_.open(wal_path_, std::ios::binary | std::ios::trunc);
        MONAD_ASSERT(cursor_);
    }

    WalEntry entry{.action = action, .id = block_id};
    cursor_.write(reinterpret_cast<char *>(&entry), sizeof(WalEntry));
    cursor_.flush();
    MONAD_ASSERT(cursor_);
}

MONAD_NAMESPACE_END
