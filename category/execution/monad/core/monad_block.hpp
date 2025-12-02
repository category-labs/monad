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

#pragma once

#include <category/core/byte_string.hpp>
#include <category/core/bytes.hpp>
#include <category/core/config.hpp>
#include <category/execution/ethereum/core/block.hpp>
#include <category/execution/ethereum/core/transaction.hpp>
#include <category/execution/ethereum/core/withdrawal.hpp>

#include <cstdint>
#include <utility>
#include <vector>

#define EXPLICIT_MONAD_CONSENSUS_BLOCK_HEADER(f)                               \
    template decltype(f<MonadConsensusBlockHeaderV0>)                          \
        f<MonadConsensusBlockHeaderV0>;                                        \
    template decltype(f<MonadConsensusBlockHeaderV1>)                          \
        f<MonadConsensusBlockHeaderV1>;                                        \
    template decltype(f<MonadConsensusBlockHeaderV2>)                          \
        f<MonadConsensusBlockHeaderV2>;

MONAD_NAMESPACE_BEGIN

struct MonadVoteV0
{
    bytes32_t id{NULL_HASH_BLAKE3};
    uint64_t round{0};
    uint64_t epoch{0};
    bytes32_t parent_id{NULL_HASH_BLAKE3};
    uint64_t parent_round{0};

    friend bool operator==(MonadVoteV0 const &, MonadVoteV0 const &) = default;
};

static_assert(sizeof(MonadVoteV0) == 88);
static_assert(alignof(MonadVoteV0) == 8);

struct MonadVoteV1
{
    bytes32_t id{NULL_HASH_BLAKE3};
    uint64_t round{0};
    uint64_t epoch{0};

    friend bool operator==(MonadVoteV1 const &, MonadVoteV1 const &) = default;
};

static_assert(sizeof(MonadVoteV1) == 48);
static_assert(alignof(MonadVoteV1) == 8);

struct MonadSignerMap
{
    uint32_t num_bits{0};
    byte_string bitmap{};

    friend bool
    operator==(MonadSignerMap const &, MonadSignerMap const &) = default;
};

static_assert(sizeof(MonadSignerMap) == 40);
static_assert(alignof(MonadSignerMap) == 8);

struct MonadSignatures
{
    MonadSignerMap signer_map{};
    byte_string_fixed<96> aggregate_signature{};

    friend bool
    operator==(MonadSignatures const &, MonadSignatures const &) = default;
};

static_assert(sizeof(MonadSignatures) == 136);
static_assert(alignof(MonadSignatures) == 8);

template <typename MonadVote>
struct MonadQuorumCertificate
{
    MonadVote vote{};
    MonadSignatures signatures{};

    friend bool operator==(
        MonadQuorumCertificate const &,
        MonadQuorumCertificate const &) = default;
};

using MonadQuorumCertificateV0 = MonadQuorumCertificate<MonadVoteV0>;
using MonadQuorumCertificateV1 = MonadQuorumCertificate<MonadVoteV1>;

static_assert(sizeof(MonadQuorumCertificateV0) == 224);
static_assert(alignof(MonadQuorumCertificateV0) == 8);

static_assert(sizeof(MonadQuorumCertificateV1) == 184);
static_assert(alignof(MonadQuorumCertificateV1) == 8);

template <class MonadQuorumCertificate>
struct MonadConsensusBlockHeader
{
    uint64_t block_round{0};
    uint64_t epoch{0};
    MonadQuorumCertificate qc{}; // qc is for the previous block
    byte_string_fixed<33> author{};
    uint64_t seqno{0};
    uint128_t timestamp_ns{0};
    byte_string_fixed<96> round_signature{};
    std::vector<BlockHeader> delayed_execution_results{};
    BlockHeaderInputs header_inputs{};
    bytes32_t block_body_id{NULL_HASH_BLAKE3};

    bytes32_t parent_id() const noexcept
    {
        return qc.vote.id;
    }

    friend bool operator==(
        MonadConsensusBlockHeader const &,
        MonadConsensusBlockHeader const &) = default;
};

using MonadConsensusBlockHeaderV0 =
    MonadConsensusBlockHeader<MonadQuorumCertificateV0>;
using MonadConsensusBlockHeaderV1 =
    MonadConsensusBlockHeader<MonadQuorumCertificateV1>;

struct MonadConsensusBlockHeaderV2 : MonadConsensusBlockHeaderV1
{
    uint64_t base_fee{0};
    uint64_t base_fee_trend{0};
    uint64_t base_fee_moment{0};

    friend bool operator==(
        MonadConsensusBlockHeaderV2 const &,
        MonadConsensusBlockHeaderV2 const &) = default;
};

static_assert(sizeof(MonadConsensusBlockHeaderV0) == 888);
static_assert(alignof(MonadConsensusBlockHeaderV0) == 8);

static_assert(sizeof(MonadConsensusBlockHeaderV1) == 848);
static_assert(alignof(MonadConsensusBlockHeaderV1) == 8);

static_assert(sizeof(MonadConsensusBlockHeaderV2) == 872);
static_assert(alignof(MonadConsensusBlockHeaderV2) == 8);

struct MonadConsensusBlockBody
{
    std::vector<Transaction> transactions{};
    std::vector<BlockHeader> ommers{}; // always empty on monad
    std::vector<Withdrawal> withdrawals{};

    friend bool operator==(
        MonadConsensusBlockBody const &,
        MonadConsensusBlockBody const &) = default;
};

static_assert(sizeof(MonadConsensusBlockBody) == 72);
static_assert(alignof(MonadConsensusBlockBody) == 8);

template <class MonadConsensusBlockHeader>
struct MonadConsensusBlock
{
    MonadConsensusBlockHeader header{};
    MonadConsensusBlockBody body{};

    friend bool operator==(
        MonadConsensusBlock const &, MonadConsensusBlock const &) = default;
};

using MonadConsensusBlockV0 = MonadConsensusBlock<MonadConsensusBlockHeaderV0>;
using MonadConsensusBlockV1 = MonadConsensusBlock<MonadConsensusBlockHeaderV1>;
using MonadConsensusBlockV2 = MonadConsensusBlock<MonadConsensusBlockHeaderV2>;

static_assert(sizeof(MonadConsensusBlockV0) == 960);
static_assert(alignof(MonadConsensusBlockV0) == 8);

static_assert(sizeof(MonadConsensusBlockV1) == 920);
static_assert(alignof(MonadConsensusBlockV1) == 8);

static_assert(sizeof(MonadConsensusBlockV2) == 944);
static_assert(alignof(MonadConsensusBlockV2) == 8);

MONAD_NAMESPACE_END
