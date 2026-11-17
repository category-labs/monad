// Copyright (C) 2025-26 Category Labs, Inc.
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

#pragma once

#include <category/core/bytes.hpp>
#include <category/core/result.hpp>
#include <category/execution/domain/config.hpp>
#include <category/mpt/ondisk_db_config.hpp>

#include <cstdint>
#include <filesystem>
#include <initializer_list>

#if __has_include(<boost/outcome/experimental/status-code/status-code/config.hpp>)
    #include <boost/outcome/experimental/status-code/status-code/config.hpp>
    #include <boost/outcome/experimental/status-code/status-code/quick_status_code_from_enum.hpp>
#else
    #include <boost/outcome/experimental/status-code/config.hpp>
    #include <boost/outcome/experimental/status-code/quick_status_code_from_enum.hpp>
#endif

MONAD_DOMAIN_NAMESPACE_BEGIN

// Statesync moves the whole state of a domain at one block from one
// monad-domain to another over a connected stream socket. The receiver names
// the block and holds its hash, which the hub attested on the L1, so it
// trusts the sender for nothing:
//
//   - the block's header must hash to the attested hash;
//   - the state must have the header's state root;
//   - the hashes of the blocks before it are in that state (EIP-2935), and
//     the headers sent for them must match.
//
// The request is `magic(32) | version(32) | domainChainId(64) |
// blockNumber(64)`, big-endian. The reply is a sequence of frames, each
// `tag(8) | type(8) | shard(16) | length(32)` followed by `length` bytes: data
// frames carry the records of a db snapshot (see db_snapshot.h), and one end
// frame closes the reply and says whether the sender could serve the block.

enum class StatesyncError
{
    Success = 0,
    // The connection failed or was closed early.
    Connection,
    // The request or the reply does not follow the protocol.
    Protocol,
    // The request is for another domain than the one the sender serves.
    WrongDomain,
    // The sender does not have the block, or could not read all of it.
    Unavailable,
    // The block's header does not hash to the attested hash.
    WrongBlockHash,
    // The state does not have the state root of the block's header.
    WrongStateRoot,
    // The header of an earlier block does not hash to what the state holds
    // for it.
    WrongBlockHistory,
};

// Serves one request on the connected socket `fd`: sends the state of the
// requested block of domain `domain_chain_id` from the db at `domain_db_path`,
// which another thread may be writing to. Fails if the reply could not be sent
// whole.
Result<void> serve_domain_state(
    int fd, uint64_t domain_chain_id,
    std::filesystem::path const &domain_db_path);

// Requests the state of block `block_number` of domain `domain_chain_id` on
// the connected socket `fd`, loads it into a new db created with `db_config`,
// and checks it against `block_hash`. The db is the domain's as of that block
// only on success: on failure it must be discarded.
Result<void> sync_domain_state(
    int fd, uint64_t domain_chain_id, uint64_t block_number,
    bytes32_t const &block_hash, mpt::OnDiskDbConfig const &db_config);

MONAD_DOMAIN_NAMESPACE_END

BOOST_OUTCOME_SYSTEM_ERROR2_NAMESPACE_BEGIN

template <>
struct quick_status_code_from_enum<monad::domain::StatesyncError>
    : quick_status_code_from_enum_defaults<monad::domain::StatesyncError>
{
    static constexpr auto const domain_name = "Domain Statesync Error";
    static constexpr auto const domain_uuid =
        "b2f4d9c1-6e0a-4a57-8b3c-1f9d2e7a4c60";

    static std::initializer_list<mapping> const &value_mappings();
};

BOOST_OUTCOME_SYSTEM_ERROR2_NAMESPACE_END
