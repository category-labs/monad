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
#include <zkvm/test/corpus/token_contracts.hpp>
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
#include <cstddef>
#include <cstring>
#include <string>
#include <string_view>
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

        /// keccak256(seed ‖ label ‖ be64(i))[12:]: an address nobody holds a
        /// key for, so a keccak and not an EC multiplication. The label keeps
        /// one role's addresses from ever meeting another's.
        Address seeded_address(
            bytes32_t const &seed, std::string_view const label,
            uint64_t const i)
        {
            byte_string buf{seed.bytes, sizeof(seed.bytes)};
            buf.append(
                reinterpret_cast<unsigned char const *>(label.data()),
                label.size());
            for (unsigned b = 0; b < 8; ++b) {
                buf.push_back(static_cast<unsigned char>(i >> (56 - 8 * b)));
            }
            auto const h = to_bytes(keccak256(buf));
            Address a;
            std::memcpy(a.bytes, h.bytes + 12, sizeof(a.bytes));
            return a;
        }

        /// A holder needs an address, not a key: nobody signs for it. So this
        /// is a keccak and not an EC multiplication -- which is what makes a
        /// million of them affordable at all.
        Address holder_address(bytes32_t const &seed, uint64_t const i)
        {
            return seeded_address(seed, "holder", i);
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

        bool is_token_preset(Preset const p)
        {
            return p == Preset::WholesaleCbdc || p == Preset::WorkerPayouts;
        }

        bool is_wholesale(Preset const p)
        {
            return p == Preset::Wholesale || p == Preset::WholesaleCbdc;
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
            if (is_token_preset(s.preset)) {
                // Every participant can be drawn; the roles' own bounds are
                // checked in resolved().
                return s.accounts;
            }
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

        /// `distinct` distinct indices in [0, n), drawn by shape from a
        /// generator started at `prng_seed`.
        ///
        /// Zipf collides heavily on its head, so the draw is capped and the
        /// shortfall filled by scanning up from index 0. That keeps the
        /// realized set head-heavy with a sampled tail -- which is what a
        /// payout run looks like -- while GUARANTEEING the distinct count,
        /// and the distinct count is the whole point: it is what the cost
        /// depends on, so a shape that quietly delivered fewer would be
        /// comparing two different experiments.
        std::vector<uint64_t> draw_seeded(
            WorkloadSpec const &spec, uint64_t const n, uint64_t const distinct,
            uint32_t const prng_seed)
        {
            MONAD_ASSERT(distinct <= n);
            small_prng rand{prng_seed};

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

        /// The native presets' draw: one per block, keyed on the block.
        std::vector<uint64_t> draw(
            WorkloadSpec const &spec, uint64_t const n, uint64_t const distinct,
            uint64_t const block)
        {
            return draw_seeded(
                spec,
                n,
                distinct,
                static_cast<uint32_t>(
                    static_cast<uint32_t>(spec.seed.bytes[0]) << 24 |
                    static_cast<uint32_t>(spec.seed.bytes[1]) << 16 |
                    static_cast<uint32_t>(block & 0xffff)));
        }

        // ---- the token presets -------------------------------------------

        /// A generator seed for one role's draw in one block. A token block
        /// draws several roles, and two draws from one seed would pick the
        /// same indices in each.
        uint32_t
        stream(bytes32_t const &seed, uint64_t const block, uint64_t const role)
        {
            byte_string buf{seed.bytes, sizeof(seed.bytes)};
            for (uint64_t const v : {block, role}) {
                for (unsigned b = 0; b < 8; ++b) {
                    buf.push_back(
                        static_cast<unsigned char>(v >> (56 - 8 * b)));
                }
            }
            auto const h = to_bytes(keccak256(buf));
            return static_cast<uint32_t>(h.bytes[0]) << 24 |
                   static_cast<uint32_t>(h.bytes[1]) << 16 |
                   static_cast<uint32_t>(h.bytes[2]) << 8 |
                   static_cast<uint32_t>(h.bytes[3]);
        }

        /// Key indices only the token presets use, apart from every range
        /// above.
        constexpr uint64_t PLATFORM_INDEX = 3'000;
        constexpr uint64_t BUSINESS_INDEX_BASE = 1'000'000;

        constexpr uint64_t TOKEN_GAS = 150'000;
        constexpr uint64_t PVP_GAS = 300'000;
        /// A payroll run, "a single instruction covering many recipients".
        constexpr uint64_t PAYROLL_BATCH = 40;
        constexpr uint64_t BATCH_GAS = 40'000 * PAYROLL_BATCH;

        /// Reserves carry eighteen decimals; the payout case's dollar tokens
        /// carry six, as USDC does.
        constexpr uint256_t USD = 1'000'000;

        /// A payment is worth `units(c)` of currency c times this, times one
        /// to five.
        uint256_t const PAYMENT_SCALE = ETHER * 1'000'000;
        uint256_t const RESERVE_REDEMPTION = PAYMENT_SCALE;
        /// Every bank starts with this many PAYMENT_SCALEs of each currency
        /// it holds. A bank is drawn at most once a block, and each draw costs
        /// it at most one payment or one redemption, so resolved() can check
        /// that a run never outspends it.
        constexpr uint64_t BANK_RESERVES_IN_SCALE = 1'000'000;
        uint256_t const BANK_RESERVES =
            PAYMENT_SCALE * uint256_t{BANK_RESERVES_IN_SCALE};

        /// The document's example salary: 2,000 USD a month.
        uint256_t const PAY = USD * 2'000;
        /// "Very many accounts holding very small balances."
        uint256_t const CONTRACTOR_BALANCE = USD * 150;
        /// Contractors who send are drawn again and again over a run, so they
        /// hold enough to spend 200 USD a block for thousands of blocks.
        uint256_t const ACTIVE_BALANCE = USD * 1'000'000;
        uint256_t const ACTIVE_SHARES = USD * 100'000;
        uint256_t const PLATFORM_FLOAT = USD * 10'000'000'000;
        uint256_t const BUSINESS_FUNDS = USD * 1'000'000'000;
        uint256_t const DEPOSIT = USD * 100;
        uint256_t const WITHDRAWAL = USD * 50;
        uint256_t const CARD_SPEND = USD * 25;
        uint256_t const REDEMPTION = USD * 200;
        uint256_t const TO_L1 = USD * 100;

        /// WholesaleCbdc's banks, by index: intermediaries first -- a tenth,
        /// holding every currency -- then each currency's own banks in turn,
        /// the rest split evenly between them.
        struct BankRoles
        {
            uint64_t intermediaries;
            uint64_t count;
            uint64_t currencies;

            /// The first bank whose currency is `c`. `currencies` gives the
            /// end.
            uint64_t begin(uint64_t const c) const
            {
                return intermediaries +
                       c * (count - intermediaries) / currencies;
            }

            uint64_t size(uint64_t const c) const
            {
                return begin(c + 1) - begin(c);
            }

            bool holds(uint64_t const bank, uint64_t const c) const
            {
                return bank < intermediaries ||
                       (bank >= begin(c) && bank < begin(c + 1));
            }
        };

        BankRoles bank_roles(WorkloadSpec const &s)
        {
            uint64_t const m = std::max<uint64_t>(2, s.accounts / 10);
            return {m, s.accounts, s.currencies};
        }

        /// What a payment is worth in each currency, per PAYMENT_SCALE: the
        /// document's 72 AAA for 60 BBB for the first two, made-up rates for
        /// the rest. They only have to be affordable.
        uint64_t units(uint64_t const c)
        {
            return c == 0 ? 72 : c == 1 ? 60 : 50 + 10 * c;
        }

        /// The stream each of a WholesaleCbdc block's draws takes: the first
        /// two currencies, then the intermediaries, then the corridors, then
        /// the currencies after the second. Adding currencies adds draws and
        /// never renumbers one a smaller platform makes.
        constexpr uint64_t INTERMEDIARY_STREAM = 2;
        constexpr uint64_t CORRIDOR_STREAM = 3;

        uint64_t currency_stream(uint64_t const c)
        {
            return c < 2 ? c : c + 2;
        }

        /// The currencies each of a block's `p` payments runs between, as
        /// (the debtor's, the creditor's). A pair is drawn with weight
        /// 1/(a+1) x 1/(b+1), so the first currency is on one side of most
        /// payments and a few corridors carry most of the volume, the way a
        /// hub currency does. Within a pair, the first half of its payments
        /// run from the lower-ranked currency to the other and the rest back,
        /// the larger half alternating from block to block: settlement flows
        /// both ways.
        std::vector<std::pair<uint64_t, uint64_t>>
        corridors(WorkloadSpec const &s, uint64_t const p, uint64_t const index)
        {
            std::vector<std::pair<uint64_t, uint64_t>> pairs;
            std::vector<double> upto;
            double total = 0.0;
            for (uint64_t a = 0; a < s.currencies; ++a) {
                for (uint64_t b = a + 1; b < s.currencies; ++b) {
                    total += 1.0 / static_cast<double>((a + 1) * (b + 1));
                    pairs.emplace_back(a, b);
                    upto.push_back(total);
                }
            }
            small_prng rand{stream(s.seed, index, CORRIDOR_STREAM)};
            std::vector<size_t> pick(p);
            std::vector<uint64_t> in_pair(pairs.size(), 0);
            for (auto &j : pick) {
                double const u =
                    (static_cast<double>(rand()) + 0.5) / 4294967296.0 * total;
                j = static_cast<size_t>(
                    std::lower_bound(upto.begin(), upto.end(), u) -
                    upto.begin());
                MONAD_ASSERT(j < pairs.size());
                ++in_pair[j];
            }
            std::vector<uint64_t> seen(pairs.size(), 0);
            std::vector<std::pair<uint64_t, uint64_t>> out;
            out.reserve(p);
            for (size_t const j : pick) {
                auto const [a, b] = pairs[j];
                bool const forward = seen[j]++ < (in_pair[j] + index % 2) / 2;
                out.emplace_back(forward ? a : b, forward ? b : a);
            }
            return out;
        }

        /// A payment touches its debtor in the block that proposes it and all
        /// three banks in the next, so a block that proposes p payments and
        /// settles the last block's p touches about 4p banks.
        uint64_t payments_per_block(WorkloadSpec const &s)
        {
            return std::max<uint64_t>(1, s.distinct / 4);
        }

        /// WorkerPayouts' contractors: a pool who send, with keys, and the
        /// many who only receive, without -- the same split, for the same
        /// reason, as signer_count and holder_count above.
        struct PayoutRoles
        {
            uint64_t active;
            uint64_t keyless;
            uint64_t businesses;
        };

        PayoutRoles payout_roles(WorkloadSpec const &s)
        {
            uint64_t const active = std::min<uint64_t>(4096, s.accounts / 2);
            return {
                active,
                s.accounts - active,
                std::max<uint64_t>(4, s.accounts / 1000)};
        }

        /// How a block's `distinct` contractors split. Most are paid; a few
        /// are admitted and paid in the same block; the rest use the vault or
        /// leave by one of the three exits.
        struct PayoutMix
        {
            uint64_t fresh;
            uint64_t paid;
            uint64_t earn;
            uint64_t exits;
            uint64_t batches;
        };

        PayoutMix payout_mix(WorkloadSpec const &s)
        {
            uint64_t const d = s.distinct;
            uint64_t const fresh = d / 50;
            uint64_t const paid = d * 80 / 100 - fresh;
            uint64_t const earn = d * 10 / 100;
            uint64_t const exits = d - fresh - paid - earn;
            return {
                fresh,
                paid,
                earn,
                exits,
                (fresh + paid + PAYROLL_BATCH - 1) / PAYROLL_BATCH};
        }

        /// Seeds one WrappedToken. Its storage has to follow its account into
        /// the same chunk (genesis_bulk.hpp), so construction writes the
        /// account and code, holders and allowances follow, and finish()
        /// writes the supply they add up to.
        class TokenSeeder
        {
        public:
            TokenSeeder(GenesisSink &sink, Address const &token)
                : sink_{sink}
                , token_{token}
            {
                sink_.contract(
                    token_, Account{.nonce = 1}, tokens::wrapped_token_code());
            }

            /// An admitted holder, with its balance.
            void holder(Address const &h, uint256_t const &balance)
            {
                sink_.storage(
                    token_,
                    tokens::balance_slot(h),
                    tokens::word(balance | tokens::ELIGIBLE));
                supply_ += balance;
            }

            /// An allowance that transferFrom never spends down.
            void unlimited(Address const &owner, Address const &spender)
            {
                sink_.storage(
                    token_,
                    tokens::allowance_slot(owner, spender),
                    tokens::word(~uint256_t{0}));
            }

            void finish(
                Address const &admin, Address const &spoke,
                Address const &l1_bridge)
            {
                // The eligibility bit and the amount share a slot; this is
                // the bound that keeps them apart.
                MONAD_ASSERT(supply_ < tokens::ELIGIBLE);
                auto const at = [](uint64_t const slot) {
                    return tokens::word(uint256_t{slot});
                };
                sink_.storage(
                    token_,
                    at(tokens::TOTAL_SUPPLY_SLOT),
                    tokens::word(supply_));
                sink_.storage(
                    token_, at(tokens::ADMIN_SLOT), tokens::word(admin));
                sink_.storage(
                    token_, at(tokens::SPOKE_SLOT), tokens::word(spoke));
                sink_.storage(
                    token_,
                    at(tokens::L1_BRIDGE_SLOT),
                    tokens::word(l1_bridge));
            }

        private:
            GenesisSink &sink_;
            Address token_;
            uint256_t supply_{0};
        };
    }

    Preset preset_from_name(std::string const &s)
    {
        if (s == "wholesale") {
            return Preset::Wholesale;
        }
        if (s == "wholesale-cbdc") {
            return Preset::WholesaleCbdc;
        }
        if (s == "worker-payouts") {
            return Preset::WorkerPayouts;
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
        switch (p) {
        case Preset::Wholesale:
            return "wholesale";
        case Preset::Payouts:
            return "payouts";
        case Preset::WholesaleCbdc:
            return "wholesale-cbdc";
        case Preset::WorkerPayouts:
            return "worker-payouts";
        }
        MONAD_ABORT("unreachable");
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
            r.accounts = is_wholesale(r.preset) ? 500 : 1'000'000;
        }
        if (r.distinct == 0) {
            r.distinct = is_wholesale(r.preset) ? 40 : 500;
        }
        if (r.preset == Preset::WholesaleCbdc && r.currencies == 0) {
            // Multi-currency settlement platforms run from four currencies
            // to seven; the document's example is one payment between two.
            r.currencies = 5;
        }
        MONAD_ASSERT_PRINTF(
            r.currencies == 0 || r.preset == Preset::WholesaleCbdc,
            "currencies=%lu: only wholesale-cbdc has currencies to count",
            r.currencies);
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
        if (r.preset == Preset::WholesaleCbdc) {
            // Not `p`: MONAD_ASSERT_PRINTF declares a `char *p` of its own,
            // which would shadow it in the argument list.
            auto const b = bank_roles(r);
            uint64_t const payments = payments_per_block(r);
            MONAD_ASSERT_PRINTF(
                r.currencies >= 2 && r.currencies < r.accounts,
                "currencies=%lu: a payment is between two, and every "
                "currency needs banks of its own",
                r.currencies);
            // A currency is on one side of a payment at most, and one bank a
            // block redeems.
            uint64_t smallest = b.size(0);
            uint64_t dearest = 0;
            for (uint64_t c = 0; c < r.currencies; ++c) {
                smallest = std::min(smallest, b.size(c));
                dearest = std::max(dearest, units(c));
            }
            MONAD_ASSERT_PRINTF(
                payments <= b.intermediaries && payments + 1 <= smallest,
                "distinct=%lu is %lu payments a block, and %lu banks over "
                "%lu currencies have %lu intermediaries and as few as %lu "
                "banks in one currency",
                r.distinct,
                payments,
                r.accounts,
                r.currencies,
                b.intermediaries,
                smallest);
            MONAD_ASSERT_PRINTF(
                r.blocks * 5 * dearest <= BANK_RESERVES_IN_SCALE,
                "blocks=%lu could spend more than a bank's reserves",
                r.blocks);
        }
        if (r.preset == Preset::WorkerPayouts) {
            auto const c = payout_roles(r);
            auto const m = payout_mix(r);
            MONAD_ASSERT_PRINTF(
                m.paid <= c.keyless && m.earn + m.exits <= c.active &&
                    m.batches <= c.businesses,
                "distinct=%lu pays %lu, moves %lu and funds %lu batches a "
                "block, and %lu contractors have %lu who only receive, %lu "
                "who send and %lu businesses",
                r.distinct,
                m.paid,
                m.earn + m.exits,
                m.batches,
                r.accounts,
                c.keyless,
                c.active,
                c.businesses);
        }
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
        if (spec_.preset == Preset::WholesaleCbdc) {
            signers_.reserve(spec_.accounts);
            for (uint64_t i = 0; i < spec_.accounts; ++i) {
                signers_.push_back(
                    address_of(derive_key(spec_.seed, SIGNER_INDEX_BASE + i)));
            }
        }
        if (spec_.preset == Preset::WorkerPayouts) {
            auto const c = payout_roles(spec_);
            signers_.reserve(c.active);
            for (uint64_t i = 0; i < c.active; ++i) {
                signers_.push_back(
                    address_of(derive_key(spec_.seed, SIGNER_INDEX_BASE + i)));
            }
            businesses_.reserve(c.businesses);
            for (uint64_t i = 0; i < c.businesses; ++i) {
                businesses_.push_back(address_of(
                    derive_key(spec_.seed, BUSINESS_INDEX_BASE + i)));
            }
        }
    }

    Address Workload::token(uint64_t const index) const
    {
        MONAD_ASSERT(
            index <
            (spec_.preset == Preset::WholesaleCbdc ? spec_.currencies : 2));
        return seeded_address(spec_.seed, "token", index);
    }

    Address Workload::settlement() const
    {
        return seeded_address(spec_.seed, "settlement", 0);
    }

    Address Workload::vault() const
    {
        return seeded_address(spec_.seed, "vault", 0);
    }

    std::function<void(GenesisSink &)> Workload::seeder() const
    {
        WorkloadSpec const spec = spec_;
        Address const deployer =
            address_of(derive_key(spec.seed, SPOKE_DEPLOYER_INDEX));
        Address const l1_bridge = seeded_address(spec.seed, "l1-bridge", 0);

        if (spec.preset == Preset::WholesaleCbdc) {
            // Banks hold the currencies they are admitted to, and every one
            // has approved the settlement contract on each, so settling a
            // payment needs no approval of its own.
            std::vector<Address> wrapped;
            for (uint64_t c = 0; c < spec.currencies; ++c) {
                wrapped.push_back(token(c));
            }
            return [spec,
                    deployer,
                    l1_bridge,
                    banks = signers_,
                    wrapped,
                    spoke = spoke(),
                    pvp = settlement()](GenesisSink &sink) {
                sink.account(deployer, Account{.balance = SIGNER_BALANCE});
                for (auto const &b : banks) {
                    sink.account(b, Account{.balance = SIGNER_BALANCE});
                }
                auto const roles = bank_roles(spec);
                for (uint64_t t = 0; t < spec.currencies; ++t) {
                    TokenSeeder token{sink, wrapped[t]};
                    for (uint64_t i = 0; i < roles.count; ++i) {
                        if (roles.holds(i, t)) {
                            token.holder(banks[i], BANK_RESERVES);
                            token.unlimited(banks[i], pvp);
                        }
                    }
                    // The central bank of that currency keeps its token's
                    // eligibility list, and acts on nothing in a block.
                    token.finish(
                        seeded_address(spec.seed, "central-bank", t),
                        spoke,
                        l1_bridge);
                }
                sink.contract(
                    pvp, Account{.nonce = 1}, tokens::pvp_settlement_code());
            };
        }

        if (spec.preset == Preset::WorkerPayouts) {
            return [spec,
                    deployer,
                    l1_bridge,
                    active = signers_,
                    businesses = businesses_,
                    spoke = spoke(),
                    vault = vault(),
                    usd = token(0),
                    fund = token(1)](GenesisSink &sink) {
                auto const roles = payout_roles(spec);
                Address const platform =
                    address_of(derive_key(spec.seed, PLATFORM_INDEX));

                sink.account(deployer, Account{.balance = SIGNER_BALANCE});
                sink.account(platform, Account{.balance = PAYER_BALANCE});
                for (auto const &b : businesses) {
                    sink.account(b, Account{.balance = SIGNER_BALANCE});
                }
                for (auto const &a : active) {
                    sink.account(a, Account{.balance = SIGNER_BALANCE});
                }

                // The contractors' dollar token. The platform keeps its
                // eligibility list: admission follows the identity check it
                // runs. A contractor who only receives has a balance slot
                // and no account at all -- nothing it does creates one.
                uint256_t const vault_assets =
                    ACTIVE_SHARES * uint256_t{active.size()};
                {
                    TokenSeeder t{sink, usd};
                    for (uint64_t i = 0; i < roles.keyless; ++i) {
                        t.holder(
                            holder_address(spec.seed, i), CONTRACTOR_BALANCE);
                    }
                    for (auto const &a : active) {
                        t.holder(a, ACTIVE_BALANCE);
                        t.unlimited(a, vault);
                    }
                    t.holder(platform, PLATFORM_FLOAT);
                    t.holder(vault, vault_assets);
                    t.holder(seeded_address(spec.seed, "card", 0), 0);
                    t.holder(seeded_address(spec.seed, "redemption", 0), 0);
                    t.finish(platform, spoke, l1_bridge);
                }
                // The businesses' stablecoin, which payroll is funded in.
                {
                    TokenSeeder t{sink, fund};
                    for (auto const &b : businesses) {
                        t.holder(b, BUSINESS_FUNDS);
                    }
                    t.holder(platform, 0);
                    t.finish(
                        seeded_address(spec.seed, "issuer", 1),
                        spoke,
                        l1_bridge);
                }

                // Every contractor who sends has been verified by the vault
                // and holds shares in it.
                auto const at = [](uint64_t const slot) {
                    return tokens::word(uint256_t{slot});
                };
                sink.contract(
                    vault, Account{.nonce = 1}, tokens::earn_vault_code());
                sink.storage(
                    vault, at(tokens::VAULT_ASSET_SLOT), tokens::word(usd));
                for (auto const &a : active) {
                    sink.storage(
                        vault,
                        tokens::vault_verified_slot(a),
                        tokens::word(uint256_t{1}));
                    sink.storage(
                        vault,
                        tokens::vault_shares_slot(a),
                        tokens::word(ACTIVE_SHARES));
                }
                sink.storage(
                    vault,
                    at(tokens::VAULT_TOTAL_SHARES_SLOT),
                    tokens::word(vault_assets));
                sink.storage(
                    vault,
                    at(tokens::VAULT_ADMIN_SLOT),
                    tokens::word(platform));
            };
        }

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

        if (spec_.preset == Preset::WholesaleCbdc) {
            return wholesale_cbdc_block(index);
        }
        if (spec_.preset == Preset::WorkerPayouts) {
            return worker_payouts_block(index);
        }

        uint64_t const signers = signer_count(spec_);
        auto const picks = draw(spec_, pool_size(spec_), spec_.distinct, index);
        auto const payer_key =
            derive_key(spec_.seed, PAYER_INDEX_BASE + (index % PAYERS));
        Address const spoke_addr = spoke();

        if (spec_.preset == Preset::Wholesale) {
            // Institutions moving large amounts between themselves, plus one
            // anchor per block -- the low-volume shape, where the anchoring
            // is the point and the transfer count is small. The picks are
            // consumed in disjoint pairs, so the block touches exactly
            // `distinct` institutions and `distinct` means the same thing it
            // means for payouts.
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

    BlockSpec Workload::wholesale_cbdc_block(uint64_t const index)
    {
        BlockSpec out{};
        auto const roles = bank_roles(spec_);
        uint64_t const p = payments_per_block(spec_);
        Address const pvp = settlement();
        auto const key = [this](uint64_t const bank) {
            return derive_key(spec_.seed, SIGNER_INDEX_BASE + bank);
        };
        ankerl::unordered_dense::set<uint64_t> touched;

        // The last block's proposals, each settled by its intermediary: both
        // legs in one transaction.
        for (auto const &pr : proposed_) {
            out.txs.push_back(call(pvp, PVP_GAS, uint256_t{0}, pr.settle));
            out.keys.push_back(key(pr.intermediary));
            touched.insert(pr.debtor);
            touched.insert(pr.intermediary);
            touched.insert(pr.creditor);
        }

        // This block's, over the corridors drawn for it. Each currency's draw
        // covers its debtors, its creditors and the bank that redeems it at
        // once, so no bank is two of them in one block.
        auto const route = corridors(spec_, p, index);
        uint64_t const redeemed = (index + 1) % spec_.currencies;
        std::vector<uint64_t> need(spec_.currencies, 0);
        for (auto const &[from, to] : route) {
            ++need[from];
            ++need[to];
        }
        ++need[redeemed];
        std::vector<std::vector<uint64_t>> drawn(spec_.currencies);
        for (uint64_t c = 0; c < spec_.currencies; ++c) {
            drawn[c] = draw_seeded(
                spec_,
                roles.size(c),
                need[c],
                stream(spec_.seed, index, currency_stream(c)));
        }
        auto const middle = draw_seeded(
            spec_,
            roles.intermediaries,
            p,
            stream(spec_.seed, index, INTERMEDIARY_STREAM));
        std::vector<uint64_t> used(spec_.currencies, 0);
        auto const take = [&](uint64_t const c) {
            return roles.begin(c) + drawn[c][used[c]++];
        };

        std::vector<Proposal> next;
        next.reserve(p);
        for (uint64_t k = 0; k < p; ++k) {
            auto const [from, to] = route[k];
            uint64_t const debtor = take(from);
            uint64_t const creditor = take(to);
            uint64_t const intermediary = middle[k];
            // At the document's rate, 60 BBB costs 72 AAA.
            uint256_t const m = PAYMENT_SCALE * uint256_t{1 + k % 5};
            tokens::Payment const pay{
                .ref = uint256_t{index} << 32 | uint256_t{k},
                .token_a = token(from),
                .debtor = signers_[debtor],
                .intermediary = signers_[intermediary],
                .amount_a = m * uint256_t{units(from)},
                .token_b = token(to),
                .creditor = signers_[creditor],
                .amount_b = m * uint256_t{units(to)}};
            out.txs.push_back(
                call(pvp, PVP_GAS, uint256_t{0}, tokens::propose(pay)));
            out.keys.push_back(key(debtor));
            touched.insert(debtor);
            next.push_back(Proposal{
                .debtor = debtor,
                .intermediary = intermediary,
                .creditor = creditor,
                .settle = tokens::settle(pay)});
        }

        // One bank a block redeems reserves to the L1, each currency in turn:
        // a burn here and a message through the spoke, so every block carries
        // an anchor.
        uint64_t const redeemer = take(redeemed);
        out.txs.push_back(call(
            token(redeemed),
            SPOKE_GAS,
            uint256_t{0},
            tokens::withdraw_to_l1(RESERVE_REDEMPTION, signers_[redeemer])));
        out.keys.push_back(key(redeemer));
        touched.insert(redeemer);

        proposed_ = std::move(next);
        last_distinct_ = touched.size();
        return out;
    }

    BlockSpec Workload::worker_payouts_block(uint64_t const index)
    {
        BlockSpec out{};
        auto const roles = payout_roles(spec_);
        auto const mix = payout_mix(spec_);
        auto const platform_key = derive_key(spec_.seed, PLATFORM_INDEX);
        Address const platform = address_of(platform_key);
        Address const usd = token(0);

        // Admission: the platform adds contractors who have passed its
        // identity check to the token's eligibility list, and pays each its
        // first salary in this block. A fresh contractor is a slot the trie
        // does not have yet.
        std::vector<Address> payees;
        payees.reserve(mix.fresh + mix.paid);
        for (uint64_t k = 0; k < mix.fresh; ++k) {
            Address const c =
                holder_address(spec_.seed, roles.keyless + onboarded_ + k);
            out.txs.push_back(call(
                usd, TOKEN_GAS, uint256_t{0}, tokens::set_eligible(c, true)));
            out.keys.push_back(platform_key);
            payees.push_back(c);
        }
        onboarded_ += mix.fresh;

        // Payroll: each batch is one business funding the platform in its
        // stablecoin, then the platform paying that batch's contractors in
        // dollar tokens with a single call.
        for (uint64_t const i : draw_seeded(
                 spec_,
                 roles.keyless,
                 mix.paid,
                 stream(spec_.seed, index, 0))) {
            payees.push_back(holder_address(spec_.seed, i));
        }
        auto const funders = draw_seeded(
            spec_, roles.businesses, mix.batches, stream(spec_.seed, index, 1));
        for (uint64_t b = 0; b < mix.batches; ++b) {
            size_t const lo = b * PAYROLL_BATCH;
            size_t const hi = std::min(payees.size(), lo + PAYROLL_BATCH);
            std::vector<Address> const to{
                payees.begin() + static_cast<std::ptrdiff_t>(lo),
                payees.begin() + static_cast<std::ptrdiff_t>(hi)};
            std::vector<uint256_t> const value(to.size(), PAY);
            out.txs.push_back(call(
                token(1),
                TOKEN_GAS,
                uint256_t{0},
                tokens::transfer(platform, PAY * uint256_t{to.size()})));
            out.keys.push_back(
                derive_key(spec_.seed, BUSINESS_INDEX_BASE + funders[b]));
            out.txs.push_back(call(
                usd,
                BATCH_GAS,
                uint256_t{0},
                tokens::batch_transfer(to, value)));
            out.keys.push_back(platform_key);
        }

        // Contractors acting on their own balances: half of the earn share
        // deposits into the vault and half withdraws; the exits split evenly
        // between card spend, redemption to local currency and a withdrawal
        // to the L1.
        auto const actors = draw_seeded(
            spec_,
            roles.active,
            mix.earn + mix.exits,
            stream(spec_.seed, index, 2));
        for (uint64_t k = 0; k < actors.size(); ++k) {
            uint64_t const a = actors[k];
            if (k < mix.earn) {
                out.txs.push_back(call(
                    vault(),
                    TOKEN_GAS,
                    uint256_t{0},
                    k % 2 == 0 ? tokens::vault_deposit(DEPOSIT)
                               : tokens::vault_withdraw(WITHDRAWAL)));
            }
            else if (uint64_t const e = (k - mix.earn) % 3; e == 0) {
                out.txs.push_back(call(
                    usd,
                    TOKEN_GAS,
                    uint256_t{0},
                    tokens::transfer(
                        seeded_address(spec_.seed, "card", 0), CARD_SPEND)));
            }
            else if (e == 1) {
                out.txs.push_back(call(
                    usd,
                    TOKEN_GAS,
                    uint256_t{0},
                    tokens::transfer(
                        seeded_address(spec_.seed, "redemption", 0),
                        REDEMPTION)));
            }
            else {
                out.txs.push_back(call(
                    usd,
                    SPOKE_GAS,
                    uint256_t{0},
                    tokens::withdraw_to_l1(TO_L1, signers_[a])));
            }
            out.keys.push_back(derive_key(spec_.seed, SIGNER_INDEX_BASE + a));
        }

        // The contractors, the businesses that funded them and the platform.
        // The vault and the two exit desks come on top.
        last_distinct_ = payees.size() + actors.size() + funders.size() + 1;
        return out;
    }
}

MONAD_NAMESPACE_END
