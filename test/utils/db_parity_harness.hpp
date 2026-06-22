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

#include <category/core/address.hpp>
#include <category/core/bytes.hpp>
#include <category/core/config.hpp>
#include <category/execution/ethereum/types/incarnation.hpp>

#include <monad/test/config.hpp>

#include <cstddef>
#include <cstdint>
#include <functional>
#include <span>
#include <string>
#include <vector>

MONAD_NAMESPACE_BEGIN
struct Db;
MONAD_NAMESPACE_END

MONAD_TEST_NAMESPACE_BEGIN

// A read to sample on both Dbs after a block. Sampled reads catch divergence
// that matching roots could still mask (a wrong value that hashes onto an
// unsampled path, or a read-path bug that the root recompute doesn't exercise).
struct SampledKey
{
    enum class Kind
    {
        account,
        storage,
        code,
    };

    Kind kind{Kind::account};
    Address address{};
    Incarnation incarnation{0, 0};
    bytes32_t slot_or_code_hash{};

    static SampledKey account_of(Address const &address)
    {
        return {.kind = Kind::account, .address = address};
    }

    static SampledKey storage_of(
        Address const &address, Incarnation const incarnation,
        bytes32_t const &slot)
    {
        return {
            .kind = Kind::storage,
            .address = address,
            .incarnation = incarnation,
            .slot_or_code_hash = slot};
    }

    static SampledKey code_of(bytes32_t const &code_hash)
    {
        return {.kind = Kind::code, .slot_or_code_hash = code_hash};
    }
};

// Outcome of comparing the two Dbs after one block. `mismatches` is empty iff
// the four roots and every sampled read agreed.
struct BlockParity
{
    uint64_t number{0};
    std::vector<std::string> mismatches{};

    bool match() const noexcept
    {
        return mismatches.empty();
    }
};

// Drives two `monad::Db` instances through the same linear block stream and,
// after each block, diffs all four roots (state / receipts / transactions /
// withdrawals) plus any sampled reads. The caller supplies a `commit_one`
// callback that commits one block to a single Db; the harness invokes it once
// per Db (each `commit()` consumes its own CommitBuilder + StateDeltas, so they
// cannot be shared) and then compares.
//
// Used MonadDB-vs-MonadDB as a self-proof in F3; one side becomes RocksDbDb at
// F9. Linear stream only -- reorg/crash scenarios are Phase 2.
class DbParityHarness
{
public:
    DbParityHarness(
        Db &reference, Db &candidate, std::string reference_label = "reference",
        std::string candidate_label = "candidate");

    // Diff the two Dbs' four roots + the given sampled reads at their current
    // (post-commit) position. Updates the block/mismatch counters.
    BlockParity
    compare(uint64_t number, std::span<SampledKey const> sampled = {});

    // Commit one block to both Dbs via `commit_one` (invoked once per Db), then
    // compare(). The Dbs are expected to be positioned at the just-finalized
    // block on return from `commit_one` (the commit_sequential() helper does
    // this).
    BlockParity on_block(
        uint64_t number, std::function<void(Db &)> const &commit_one,
        std::span<SampledKey const> sampled = {});

    std::size_t blocks() const noexcept
    {
        return blocks_;
    }

    std::size_t mismatched_blocks() const noexcept
    {
        return mismatched_blocks_;
    }

    bool ok() const noexcept
    {
        return mismatched_blocks_ == 0;
    }

private:
    Db &reference_;
    Db &candidate_;
    std::string reference_label_;
    std::string candidate_label_;
    std::size_t blocks_{0};
    std::size_t mismatched_blocks_{0};
};

MONAD_TEST_NAMESPACE_END
