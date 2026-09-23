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

#include <zkvm/test/corpus/contracts/namespace_spoke_bytecode.hpp>
#include <zkvm/test/corpus/genesis_bulk.hpp>
#include <zkvm/test/corpus/scenarios.hpp>
#include <zkvm/test/corpus/tx_sign.hpp>
#include <zkvm/test/corpus/workload.hpp>

#include <category/core/assert.h>
#include <category/core/hex.hpp>
#include <category/core/keccak.hpp>
#include <category/core/small_prng.hpp>
#include <category/execution/ethereum/core/account.hpp>
#include <category/execution/ethereum/core/rlp/address_rlp.hpp>
#include <category/execution/ethereum/core/rlp/int_rlp.hpp>
#include <category/execution/ethereum/core/transaction.hpp>
#include <category/execution/ethereum/rlp/encode2.hpp>

#include <ankerl/unordered_dense.h>

#include <algorithm>
#include <cmath>
#include <cstring>
#include <string>
#include <utility>

MONAD_ANONYMOUS_NAMESPACE_BEGIN

using namespace monad;

byte_string hex_bytes(std::string_view const s)
{
    MONAD_ASSERT(s.size() % 2 == 0);
    byte_string out;
    out.reserve(s.size() / 2);
    for (size_t i = 0; i < s.size(); i += 2) {
        auto const hi = from_hex_char(s[i]);
        auto const lo = from_hex_char(s[i + 1]);
        MONAD_ASSERT(hi.has_value() && lo.has_value());
        out.push_back(
            static_cast<unsigned char>((hi.value() << 4) | lo.value()));
    }
    return out;
}

void push_word(byte_string &out, uint256_t const &v)
{
    auto const w = store_be_as<bytes32_t>(v);
    out.append(w.bytes, sizeof(w.bytes));
}

void push_word(byte_string &out, Address const &a)
{
    out.append(12, 0);
    out.append(a.bytes, sizeof(a.bytes));
}

/// sendNamespaceMessage(address,bytes) -- the selector and the ABI shape are
/// the ones scenarios.cpp already drives the same contract with.
byte_string spoke_send_calldata(Address const &to, byte_string_view payload)
{
    byte_string out{hex_bytes("acc30635")};
    push_word(out, to);
    push_word(out, uint256_t{0x40});
    push_word(out, uint256_t{payload.size()});
    out.append(payload);
    if (auto const rem = payload.size() % 32; rem != 0) {
        out.append(32 - rem, 0);
    }
    return out;
}

MONAD_ANONYMOUS_NAMESPACE_END

MONAD_NAMESPACE_BEGIN

namespace corpus
{
    namespace
    {
        constexpr uint64_t MAX_FEE = 100;
        constexpr uint64_t PRIORITY_FEE = 1;
        constexpr uint64_t TRANSFER_GAS = 21'000;
        constexpr uint64_t SPOKE_GAS = 300'000;
        constexpr uint64_t DEPLOY_GAS = 2'000'000;

        /// Payers fan out. More than one so a run is not a single account's
        /// nonce sequence, which would be a shape of its own.
        constexpr uint64_t PAYERS = 4;

        /// Key indices. Kept apart from scenarios.cpp's 0..19 / 100..109 /
        /// 200..204 so a workload and a scenario can share a seed without
        /// sharing an account. 200 is the exception and it is deliberate: it
        /// is the spoke deployer, and `--spoke-address` prints the address
        /// derived from exactly that key at nonce 0, so a compiled
        /// MONAD_ZKVM_L2_SPOKE has to keep naming it.
        constexpr uint64_t SPOKE_DEPLOYER_INDEX = 200;
        constexpr uint64_t PAYER_INDEX_BASE = 1'000;
        constexpr uint64_t SIGNER_INDEX_BASE = 2'000'000;

        /// A payer has to fund every block of the run; a signer only pays gas
        /// and sends small amounts; a holder only has to EXIST, which is the
        /// real constraint -- an account with zero balance, zero nonce and no
        /// code is empty under YP (14), so it would not be in the trie at all
        /// and a transfer to it would be an insert rather than an update.
        /// That is a different witness shape, and not the one a payouts L2
        /// with a million existing holders has.
        constexpr uint256_t ETHER = 1'000'000'000'000'000'000;
        uint256_t const PAYER_BALANCE = ETHER * 1'000'000;
        uint256_t const SIGNER_BALANCE = ETHER * 100;
        uint256_t const HOLDER_BALANCE = ETHER / 1000;

        /// A holder needs an address, not a key: nobody signs for it. So this
        /// is a keccak and not an EC multiplication -- which is what makes a
        /// million of them affordable at all.
        Address holder_address(bytes32_t const &seed, uint64_t const i)
        {
            byte_string buf{seed.bytes, sizeof(seed.bytes)};
            buf.append(reinterpret_cast<unsigned char const *>("holder"), 6);
            for (unsigned b = 0; b < 8; ++b) {
                buf.push_back(static_cast<unsigned char>(i >> (56 - 8 * b)));
            }
            auto const h = to_bytes(keccak256(buf));
            Address a;
            std::memcpy(a.bytes, h.bytes + 12, sizeof(a.bytes));
            return a;
        }

        Transaction call(
            std::optional<Address> to, uint64_t const gas,
            uint256_t const value, byte_string data)
        {
            Transaction tx{
                .max_fee_per_gas = MAX_FEE,
                .gas_limit = gas,
                .value = value,
                .to = to,
                .type = TransactionType::eip1559,
                .data = std::move(data),
                .max_priority_fee_per_gas = PRIORITY_FEE};
            tx.sc.chain_id = 1;
            return tx;
        }

        /// Signers per preset. Wholesale institutions all send, so they are
        /// all signers; a payouts holder does not, so only a pool of them is
        /// given keys -- each key costs an EC multiplication, and a million
        /// would cost a minute for nothing.
        uint64_t signer_count(WorkloadSpec const &s)
        {
            if (s.preset == Preset::Wholesale) {
                return s.accounts - PAYERS - 1;
            }
            return std::min<uint64_t>(4096, (s.accounts - PAYERS - 1) / 2);
        }

        uint64_t holder_count(WorkloadSpec const &s)
        {
            return s.accounts - PAYERS - 1 - signer_count(s);
        }

        /// The accounts a block's draw addresses. The two presets differ
        /// here, which is the whole of their difference. A wholesale
        /// institution both sends and receives, so the pool IS the signer
        /// set; a payouts holder only receives, so the pool is the keyless
        /// holders and the senders come from elsewhere.
        uint64_t pool_size(WorkloadSpec const &s)
        {
            return s.preset == Preset::Wholesale ? signer_count(s)
                                                 : holder_count(s);
        }

        Address pool_address(WorkloadSpec const &s, uint64_t const i)
        {
            if (s.preset == Preset::Wholesale) {
                return address_of(derive_key(s.seed, SIGNER_INDEX_BASE + i));
            }
            return holder_address(s.seed, i);
        }

        /// `distinct` distinct indices in [0, n), drawn by shape.
        ///
        /// Zipf collides heavily on its head, so the draw is capped and the
        /// shortfall filled by scanning up from index 0. That keeps the
        /// realized set head-heavy with a sampled tail -- which is what a
        /// payout run looks like -- while GUARANTEEING the distinct count,
        /// and the distinct count is the whole point: it is what the cost
        /// depends on, so a shape that quietly delivered fewer would be
        /// comparing two different experiments.
        std::vector<uint64_t> draw(
            WorkloadSpec const &spec, uint64_t const n, uint64_t const distinct,
            uint64_t const block)
        {
            MONAD_ASSERT(distinct <= n);
            small_prng rand{static_cast<uint32_t>(
                static_cast<uint32_t>(spec.seed.bytes[0]) << 24 |
                static_cast<uint32_t>(spec.seed.bytes[1]) << 16 |
                static_cast<uint32_t>(block & 0xffff))};

            ankerl::unordered_dense::set<uint64_t> seen;
            seen.reserve(distinct);
            std::vector<uint64_t> out;
            out.reserve(distinct);

            // The continuous inverse-CDF of a Zipf over [1, n]: with
            // exponent s, x = ((n^(1-s) - 1) u + 1)^(1/(1-s)).
            double const one_minus_s = 1.0 - spec.zipf_s;
            double const n_pow = std::pow(static_cast<double>(n), one_minus_s);
            uint64_t const hot = std::min(n, distinct * 4);

            auto const pick = [&]() -> uint64_t {
                switch (spec.shape) {
                case Shape::Uniform:
                    return rand() % n;
                case Shape::HotSet:
                    return rand() % hot;
                case Shape::Zipf: {
                    double const u =
                        (static_cast<double>(rand()) + 0.5) / 4294967296.0;
                    double const x =
                        std::pow((n_pow - 1.0) * u + 1.0, 1.0 / one_minus_s);
                    double const idx = std::floor(x) - 1.0;
                    return idx <= 0.0 ? 0
                                      : std::min<uint64_t>(
                                            n - 1, static_cast<uint64_t>(idx));
                }
                }
                MONAD_ABORT("unknown access shape");
            };

            uint64_t const attempts = distinct * 8 + 64;
            for (uint64_t a = 0; a < attempts && out.size() < distinct; ++a) {
                if (uint64_t const i = pick(); seen.insert(i).second) {
                    out.push_back(i);
                }
            }
            for (uint64_t i = 0; out.size() < distinct; ++i) {
                MONAD_ASSERT(i < n);
                if (seen.insert(i).second) {
                    out.push_back(i);
                }
            }
            return out;
        }
    }

    Preset preset_from_name(std::string const &s)
    {
        if (s == "wholesale") {
            return Preset::Wholesale;
        }
        MONAD_ASSERT_PRINTF(s == "payouts", "unknown preset '%s'", s.c_str());
        return Preset::Payouts;
    }

    Shape shape_from_name(std::string const &s)
    {
        if (s == "uniform") {
            return Shape::Uniform;
        }
        if (s == "hotset") {
            return Shape::HotSet;
        }
        MONAD_ASSERT_PRINTF(s == "zipf", "unknown shape '%s'", s.c_str());
        return Shape::Zipf;
    }

    char const *name_of(Preset const p)
    {
        return p == Preset::Wholesale ? "wholesale" : "payouts";
    }

    char const *name_of(Shape const s)
    {
        switch (s) {
        case Shape::Uniform:
            return "uniform";
        case Shape::HotSet:
            return "hotset";
        case Shape::Zipf:
            return "zipf";
        }
        MONAD_ABORT("unreachable");
    }

    WorkloadSpec WorkloadSpec::resolved() const
    {
        WorkloadSpec r = *this;
        if (r.accounts == 0) {
            // Wholesale is the design document's hundreds of institutions;
            // payouts is its 1.5M-per-payer scale, rounded to a round number
            // so a sweep is readable.
            r.accounts = r.preset == Preset::Wholesale ? 500 : 1'000'000;
        }
        if (r.distinct == 0) {
            r.distinct = r.preset == Preset::Wholesale ? 40 : 500;
        }
        MONAD_ASSERT(r.accounts > PAYERS + 2);
        MONAD_ASSERT(r.chunk > 0);
        MONAD_ASSERT(r.zipf_s > 1.0);
        MONAD_ASSERT_PRINTF(
            r.distinct <= pool_size(r),
            "distinct=%lu exceeds the %lu drawable accounts a %lu-account %s "
            "state has",
            r.distinct,
            pool_size(r),
            r.accounts,
            name_of(r.preset));
        return r;
    }

    uint64_t WorkloadSpec::gas_limit() const
    {
        auto const r = resolved();
        // A transfer is 21k and a spoke call a few hundred k; 40k per
        // intended distinct account carries both with room, and the header's
        // limit is constant for the chain so it has to carry the worst block.
        return std::max<uint64_t>(GAS_LIMIT, 40'000 * r.distinct + DEPLOY_GAS);
    }

    Workload::Workload(WorkloadSpec spec)
        : spec_{spec.resolved()}
    {
    }

    std::function<void(GenesisSink &)> Workload::seeder() const
    {
        WorkloadSpec const spec = spec_;
        return [spec](GenesisSink &sink) {
            sink.account(
                address_of(derive_key(spec.seed, SPOKE_DEPLOYER_INDEX)),
                Account{.balance = SIGNER_BALANCE});
            for (uint64_t i = 0; i < PAYERS; ++i) {
                sink.account(
                    address_of(derive_key(spec.seed, PAYER_INDEX_BASE + i)),
                    Account{.balance = PAYER_BALANCE});
            }
            uint64_t const signers = signer_count(spec);
            for (uint64_t i = 0; i < signers; ++i) {
                sink.account(
                    address_of(derive_key(spec.seed, SIGNER_INDEX_BASE + i)),
                    Account{.balance = SIGNER_BALANCE});
            }
            uint64_t const holders = holder_count(spec);
            for (uint64_t i = 0; i < holders; ++i) {
                sink.account(
                    holder_address(spec.seed, i),
                    Account{.balance = HOLDER_BALANCE});
            }
        };
    }

    Address Workload::spoke() const
    {
        // keccak256(rlp([deployer, 0]))[12:] -- a CREATE from the deployer at
        // nonce 0, which is what the deploy block spends that account's first
        // transaction on. Derived here rather than read from the builder so a
        // caller can configure MONAD_ZKVM_L2_SPOKE before any block runs; the
        // deploy block asserts the builder agrees, which turns the duplicated
        // derivation into a check instead of a second source of truth.
        auto const deployer =
            address_of(derive_key(spec_.seed, SPOKE_DEPLOYER_INDEX));
        byte_string enc;
        enc += rlp::encode_address(deployer);
        enc += rlp::encode_unsigned(uint64_t{0});
        auto const h = to_bytes(keccak256(rlp::encode_list2(enc)));
        Address a;
        std::memcpy(a.bytes, h.bytes + 12, sizeof(a.bytes));
        return a;
    }

    uint64_t Workload::block_count() const
    {
        return spec_.blocks + 1;
    }

    BlockSpec Workload::block(CorpusBuilder &b, uint64_t const index)
    {
        BlockSpec out{};
        if (index >= block_count()) {
            return out;
        }

        auto const deployer_key = derive_key(spec_.seed, SPOKE_DEPLOYER_INDEX);
        if (index == 0) {
            MONAD_ASSERT(
                b.next_contract_address(address_of(deployer_key)) == spoke());
            // The deploy block. Constructor arguments are appended to the
            // creation bytecode: (uint64 namespaceChainId, address operator).
            byte_string data = hex_bytes(NAMESPACE_SPOKE_CREATION_HEX);
            push_word(data, uint256_t{1});
            push_word(
                data, address_of(derive_key(spec_.seed, PAYER_INDEX_BASE)));
            out.txs.push_back(
                call(std::nullopt, DEPLOY_GAS, uint256_t{0}, std::move(data)));
            out.keys.push_back(deployer_key);
            last_distinct_ = 2;
            return out;
        }

        uint64_t const signers = signer_count(spec_);
        auto const picks = draw(spec_, pool_size(spec_), spec_.distinct, index);
        auto const payer_key =
            derive_key(spec_.seed, PAYER_INDEX_BASE + (index % PAYERS));
        Address const spoke_addr = spoke();

        if (spec_.preset == Preset::Wholesale) {
            // Institutions moving large amounts between themselves, plus one
            // anchor per block -- the MVP shape, where the anchoring is the
            // point and the transfer count is small. The picks are consumed in
            // disjoint pairs, so the block touches exactly `distinct`
            // institutions and `distinct` means the same thing it means for
            // payouts.
            uint64_t const n = spec_.distinct / 2;
            for (uint64_t i = 0; i < n; ++i) {
                out.txs.push_back(call(
                    pool_address(spec_, picks[2 * i + 1]),
                    TRANSFER_GAS,
                    uint256_t{1'000'000'000},
                    byte_string{}));
                out.keys.push_back(
                    derive_key(spec_.seed, SIGNER_INDEX_BASE + picks[2 * i]));
            }
            out.txs.push_back(call(
                spoke_addr,
                SPOKE_GAS,
                uint256_t{0},
                spoke_send_calldata(
                    pool_address(spec_, picks[0]),
                    byte_string(
                        32, static_cast<unsigned char>(index & 0xff)))));
            out.keys.push_back(
                derive_key(spec_.seed, SIGNER_INDEX_BASE + picks[0]));
            last_distinct_ = 2 * n + 1 + 1;
            return out;
        }

        // Payouts: 85% of the block is one payer fanning out, 10% is a
        // beneficiary moving on its own, 5% is a withdrawal through the spoke.
        // The payer is one account for the whole fan-out, so the distinct
        // count the block reaches is dominated by the recipients -- which is
        // the point of drawing them.
        uint64_t const n = spec_.distinct;
        uint64_t const fan_out = n * 85 / 100;
        uint64_t const onward = n * 10 / 100;
        for (uint64_t i = 0; i < fan_out; ++i) {
            out.txs.push_back(call(
                pool_address(spec_, picks[i]),
                TRANSFER_GAS,
                uint256_t{1'000 + i},
                byte_string{}));
            out.keys.push_back(payer_key);
        }
        for (uint64_t i = 0; i < onward; ++i) {
            uint64_t const p = picks[fan_out + i];
            out.txs.push_back(call(
                pool_address(spec_, picks[(fan_out + i + 1) % n]),
                TRANSFER_GAS,
                uint256_t{7},
                byte_string{}));
            out.keys.push_back(
                derive_key(spec_.seed, SIGNER_INDEX_BASE + (p % signers)));
        }
        for (uint64_t i = fan_out + onward; i < n; ++i) {
            out.txs.push_back(call(
                spoke_addr,
                SPOKE_GAS,
                uint256_t{0},
                spoke_send_calldata(
                    pool_address(spec_, picks[i]),
                    byte_string(
                        8, static_cast<unsigned char>((index + i) & 0xff)))));
            out.keys.push_back(derive_key(
                spec_.seed, SIGNER_INDEX_BASE + (picks[i] % signers)));
        }
        last_distinct_ = n + 2;
        return out;
    }
}

MONAD_NAMESPACE_END
