// Copyright (C) 2026 Category Labs, Inc.
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

// A benchmark corpus at scale: a large genesis, then blocks that move value
// around it, shaped after the two use cases the L2 design document names.
//
// The axis is `distinct` -- how many distinct accounts a block touches -- and
// that choice is a measurement, not a preference. Over 504 mainnet witnesses
// joined to their measured cost, 82% of a witness is 33-byte digests of
// siblings the block never touched, and cost tracks witness bytes with
// R2 0.94. A leaf touched twice in one block is free: it is already in the
// witness. So the shape of the access distribution can only matter through the
// number of DISTINCT leaves it produces -- which is why `distinct` is the
// parameter swept, and why `shape` exists to TEST that prediction rather than
// to choose between hypotheses. Two shapes at equal `distinct` should cost the
// same; if they do not, the reasoning above is wrong and that is a result.

#include <category/core/address.hpp>
#include <category/core/byte_string.hpp>
#include <category/core/bytes.hpp>
#include <category/core/config.hpp>
#include <category/core/int.hpp>
#include <zkvm/test/corpus/corpus_builder.hpp>

#include <cstdint>
#include <string>
#include <vector>

MONAD_NAMESPACE_BEGIN

namespace corpus
{
    class GenesisSink;

    /// Which of the design document's two inverse cases to generate. They are
    /// inverse in the parameter that costs: wholesale is hundreds of accounts
    /// moving large amounts, payouts is over a million holders one payer fans
    /// out to. The first is the MVP, the second sets the sizing.
    enum class Preset
    {
        Wholesale,
        Payouts,
    };

    /// How a block picks the accounts it touches. Uniform is the pessimistic
    /// bound -- no two draws share a trie path below the top few levels. Zipf
    /// concentrates on a head, which is what a real payout run looks like.
    /// HotSet draws from a fixed subset, which models "how many distinct
    /// beneficiaries per block" without committing to a law.
    enum class Shape
    {
        Uniform,
        Zipf,
        HotSet,
    };

    Preset preset_from_name(std::string const &);
    Shape shape_from_name(std::string const &);
    char const *name_of(Preset);
    char const *name_of(Shape);

    struct WorkloadSpec
    {
        Preset preset{Preset::Payouts};
        Shape shape{Shape::Zipf};
        /// Accounts in the genesis state. Zero means "the preset's own
        /// default" -- zero accounts is meaningless, so it carries no other
        /// reading, and `resolved()` is what turns it into a number.
        uint64_t accounts{0};
        /// Blocks to emit after the deploy block.
        uint64_t blocks{200};
        /// Distinct accounts a block aims to touch. THE axis. Zero means the
        /// preset's default, as above.
        uint64_t distinct{0};
        double zipf_s{1.1};
        /// Accounts per genesis commit. See genesis_bulk.hpp: a StateDelta is
        /// 752 bytes whether or not the account has storage.
        size_t chunk{100'000};
        bytes32_t seed{};

        /// The defaults the preset implies, applied for any field the caller
        /// left at its own default. Returns a spec with nothing left implicit.
        WorkloadSpec resolved() const;

        /// A gas limit that fits `distinct` transfers with room to spare. A
        /// block touching thousands of accounts does not fit under 30M, and
        /// the header's limit is constant for the chain.
        uint64_t gas_limit() const;
    };

    /// Fill a genesis with this workload's accounts. Deterministic in
    /// `spec.seed`.
    void seed_workload(GenesisSink &, WorkloadSpec const &);

    /// Drives a builder through the workload's blocks, emitting each. Block 0
    /// of the run deploys the NamespaceSpoke -- from the same key and nonce
    /// `--spoke-address` prints, so a compiled MONAD_ZKVM_L2_SPOKE stays
    /// valid -- and is reported like any other, since it is a real block.
    class Workload
    {
    public:
        explicit Workload(WorkloadSpec);

        /// The genesis seeder to hand CorpusBuilder's bulk constructor.
        std::function<void(GenesisSink &)> seeder() const;

        /// The spoke address, known before any block runs because CREATE
        /// addresses are a function of deployer and nonce.
        Address spoke() const;

        /// The next block's transactions, or an empty spec once the run is
        /// done. `index` counts from 0, and 0 is the deploy block.
        BlockSpec block(CorpusBuilder &, uint64_t index);

        /// Total blocks the run emits, deploy block included.
        uint64_t block_count() const;

        WorkloadSpec const &spec() const
        {
            return spec_;
        }

        /// Distinct accounts the last `block()` call aimed to touch, before
        /// execution. The witness's own count is the measurement; this is what
        /// was asked for, and the two differing is worth seeing.
        uint64_t last_intended_distinct() const
        {
            return last_distinct_;
        }

    private:
        WorkloadSpec spec_;
        uint64_t last_distinct_{0};
    };
}

MONAD_NAMESPACE_END
