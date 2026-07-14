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

#include <category/core/address.hpp>
#include <category/core/config.hpp>
#include <category/core/log.hpp>
#include <category/execution/ethereum/core/fmt/address_fmt.hpp>
#include <category/execution/ethereum/core/fmt/int_fmt.hpp>
#include <category/execution/ethereum/metrics/block_metrics.hpp>

#include <ankerl/unordered_dense.h>

#include <algorithm>
#include <cstdint>
#include <string>
#include <vector>

MONAD_NAMESPACE_BEGIN

/// Rolling per-account activity window backing the `__tx` research log line.
/// Remembers each account's most recent transaction, applied authorization,
/// and reserve dip over the last `WINDOW` blocks, and prints one line per
/// transaction that dips, sits within `value` of the default reserve,
/// carries authorizations, or whose sender recently dipped or was the
/// subject of an applied authorization. Gap fields report distances in
/// blocks (0 = same block); authorization entries carry the authority's own
/// recent-transaction/dip gaps when within the window.
class TxActivityLog
{
public:
    static constexpr uint64_t WINDOW = 32;

    /// The protocol's default reserve (10 MON): transactions whose sender
    /// balance is within `value` of it are logged as would-be-emptying
    /// candidates, which also covers every sub-reserve sender that moves
    /// value.
    static constexpr uint256_t DEFAULT_RESERVE{10'000'000'000'000'000'000ULL};

private:
    struct Recent
    {
        // most recent block number + 1 per event kind; 0 = never seen
        uint64_t tx{0};
        uint64_t auth{0};
        uint64_t dip{0};
    };

    ankerl::unordered_dense::segmented_map<Address, Recent> recent_{};

    /// Gap in blocks + 1 between `block_number` and the stored event, or 0
    /// when the event never happened or fell out of the window.
    static uint64_t gap1(uint64_t const block_number, uint64_t const last)
    {
        if (last == 0 || block_number + 1 - last > WINDOW) {
            return 0;
        }
        return block_number + 2 - last;
    }

public:
    void record_block(uint64_t const block_number, BlockMetrics const &metrics)
    {
        for (TxRecord const &r : metrics.tx_records) {
            uint64_t gt = 0;
            uint64_t ga = 0;
            uint64_t gd = 0;
            if (auto const it = recent_.find(r.sender); it != recent_.end()) {
                gt = gap1(block_number, it->second.tx);
                ga = gap1(block_number, it->second.auth);
                gd = gap1(block_number, it->second.dip);
            }
            // Overflow-safe form of balance_before < DEFAULT_RESERVE + value:
            // merged-but-reverted transactions can carry arbitrary values.
            bool const near_reserve =
                r.balance_before < DEFAULT_RESERVE ||
                r.balance_before - DEFAULT_RESERVE < r.value;
            if (r.dipped || near_reserve || !r.auths.empty() || ga != 0 ||
                gd != 0) {
                std::string line = fmt::format(
                    "__tx,bl={},i={},s={},n={},st={},b={},ba={},v={},cd={},"
                    "dp={},dg={}",
                    block_number,
                    r.index,
                    r.sender,
                    r.nonce,
                    r.success ? 1 : 0,
                    r.balance_before,
                    r.balance_after,
                    r.value,
                    r.eligible ? 1 : 0,
                    r.dipped ? 1 : 0,
                    r.sender_delegated ? 1 : 0);
                if (gt != 0) {
                    line += fmt::format(",gt={}", gt - 1);
                }
                if (ga != 0) {
                    line += fmt::format(",ga={}", ga - 1);
                }
                if (gd != 0) {
                    line += fmt::format(",gd={}", gd - 1);
                }
                if (!r.auths.empty()) {
                    line += ",au=";
                    bool first = true;
                    for (TxAuthOutcome const &a : r.auths) {
                        if (!first) {
                            line += ';';
                        }
                        first = false;
                        if (a.authority.has_value()) {
                            line += fmt::format("{}", *a.authority);
                        }
                        else {
                            line += '?';
                        }
                        line += ':';
                        line += a.outcome;
                        if (a.authority.has_value()) {
                            if (auto const jt = recent_.find(*a.authority);
                                jt != recent_.end()) {
                                if (auto const t =
                                        gap1(block_number, jt->second.tx)) {
                                    line += fmt::format(":t{}", t - 1);
                                }
                                if (auto const d =
                                        gap1(block_number, jt->second.dip)) {
                                    line += fmt::format(":d{}", d - 1);
                                }
                            }
                        }
                    }
                }
                LOG_INFO("{}", line);
            }
            // Update after printing so same-block gaps read as 0 for later
            // transactions of this block.
            Recent &rec = recent_[r.sender];
            rec.tx = block_number + 1;
            if (r.dipped) {
                rec.dip = block_number + 1;
            }
            for (TxAuthOutcome const &a : r.auths) {
                if (a.authority.has_value() && a.outcome != 'f') {
                    recent_[*a.authority].auth = block_number + 1;
                }
            }
        }
        // Prune accounts whose every event fell out of the window.
        std::vector<Address> stale;
        for (auto const &[addr, v] : recent_) {
            if (gap1(block_number, std::max({v.tx, v.auth, v.dip})) == 0) {
                stale.push_back(addr);
            }
        }
        for (Address const &addr : stale) {
            recent_.erase(addr);
        }
    }
};

MONAD_NAMESPACE_END
