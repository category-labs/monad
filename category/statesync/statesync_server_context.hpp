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
#include <category/core/config.hpp>
#include <category/execution/ethereum/db/db.hpp>
#include <category/mpt/db.hpp>

#include <array>
#include <deque>
#include <functional>
#include <mutex>
#include <vector>

MONAD_NAMESPACE_BEGIN

inline constexpr size_t MAX_ENTRIES = 43'200;
inline constexpr size_t MAX_DELETIONS = 2'000'000;

struct Deletion
{
    Address address;
    std::optional<bytes32_t> key;

    friend bool operator==(Deletion const &, Deletion const &) = default;
};

static_assert(sizeof(Deletion) == 53);
static_assert(alignof(Deletion) == 1);

struct FinalizedDeletionsEntry
{
    std::mutex mutex{};
    uint64_t block_number{mpt::INVALID_BLOCK_NUM};
    size_t idx{0};
    size_t size{0};
};

static_assert(sizeof(FinalizedDeletionsEntry) == 64);
static_assert(alignof(FinalizedDeletionsEntry) == 8);

class FinalizedDeletions
{
    uint64_t start_block_number_{mpt::INVALID_BLOCK_NUM};
    uint64_t end_block_number_{mpt::INVALID_BLOCK_NUM};
    std::array<FinalizedDeletionsEntry, MAX_ENTRIES> entries_{};
    std::array<Deletion, MAX_DELETIONS> deletions_{};
    size_t free_start_{0};
    size_t free_end_{MAX_DELETIONS};

    void
    set_entry(uint64_t i, uint64_t block_number, std::vector<Deletion> const &);
    void clear_entry(uint64_t i);

public:
    bool for_each(uint64_t block_number, std::function<void(Deletion const &)>);
    void write(uint64_t block_number, std::vector<Deletion> const &);
};

static_assert(sizeof(FinalizedDeletions) == 108764832);
static_assert(alignof(FinalizedDeletions) == 8);

struct ProposedDeletions
{
    uint64_t block_number;
    bytes32_t block_id;
    std::vector<Deletion> deletions;
};

static_assert(sizeof(ProposedDeletions) == 64);
static_assert(alignof(ProposedDeletions) == 8);

struct CallFrame;
class TrieDb;

MONAD_NAMESPACE_END

struct monad_statesync_server_context final : public monad::Db
{
    monad::TrieDb &rw;
    monad::mpt::Db *ro;
    std::deque<monad::ProposedDeletions> proposals;
    monad::FinalizedDeletions deletions;

    explicit monad_statesync_server_context(monad::TrieDb &rw);

    virtual std::optional<monad::Account>
    read_account(monad::Address const &addr) override;

    virtual monad::bytes32_t read_storage(
        monad::Address const &addr, monad::Incarnation,
        monad::bytes32_t const &key) override;

    virtual monad::vm::SharedIntercode
    read_code(monad::bytes32_t const &hash) override;

    virtual monad::BlockHeader read_eth_header() override;

    virtual monad::bytes32_t state_root() override;

    virtual monad::bytes32_t receipts_root() override;

    virtual monad::bytes32_t transactions_root() override;

    virtual std::optional<monad::bytes32_t> withdrawals_root() override;

    virtual void set_block_and_prefix(
        uint64_t block_number,
        monad::bytes32_t const &block_id = monad::bytes32_t{}) override;
    virtual void
    finalize(uint64_t block_number, monad::bytes32_t const &block_id) override;
    virtual void update_verified_block(uint64_t block_number) override;
    virtual void update_voted_metadata(
        uint64_t block_number, monad::bytes32_t const &block_id) override;
    virtual void update_proposed_metadata(
        uint64_t block_number, monad::bytes32_t const &block_id) override;

    virtual void commit(
        monad::StateDeltas const &state_deltas, monad::Code const &code,
        monad::bytes32_t const &block_id, monad::BlockHeader const &,
        std::vector<monad::Receipt> const &receipts = {},
        std::vector<std::vector<monad::CallFrame>> const & = {},
        std::vector<monad::Address> const & = {},
        std::vector<monad::Transaction> const &transactions = {},
        std::vector<monad::BlockHeader> const &ommers = {},
        std::optional<std::vector<monad::Withdrawal>> const & =
            std::nullopt) override;

    virtual uint64_t get_block_number() const override;
};
