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

// Slot taint: dynamically detect storage slots whose use within a
// transaction is delta-commutative — the loaded value flows through ADD/SUB
// with untainted operands back into an SSTORE of the same slot, with
// comparisons, AND masks and SHR extractions recorded as constraints that
// are re-checked at merge time. Any other use revokes the slot. The merge
// validation (State::slot_delta_fixable / apply_slot_delta) consults the
// registry and, when the constraints and the zero/non-zero gas classes hold
// at the actual base value, shifts the original and current values by the
// drift instead of re-executing.

#include <category/core/runtime/uint256.hpp>

#include <evmc/evmc.hpp>

#include <array>
#include <cstdint>
#include <cstdlib>
#include <deque>
#include <map>
#include <utility>
#include <vector>

namespace monad::vm::runtime
{
    // A comparison observed on a tainted value: re-evaluated at merge time
    // against the actual base; the outcome must not change. For tainted
    // operands, lhs/rhs hold the linear offset vs the slot's txn-start value;
    // for untainted operands they hold the concrete value.
    // Constraint kinds beyond the comparison opcodes:
    //   MASK_PASS    ((x) & ~rhs) == 0     -- identity AND, taint passes
    //   MASK_EXTRACT ((x) & rhs) == expected
    //   SHR_EXTRACT  ((x) >> rhs) == expected
    inline constexpr uint8_t TAINT_MASK_PASS = 0xf0;
    inline constexpr uint8_t TAINT_MASK_EXTRACT = 0xf1;
    inline constexpr uint8_t TAINT_SHR_EXTRACT = 0xf2;

    struct TaintConstraint
    {
        uint8_t kind; // EVM opcode LT/GT/SLT/SGT/EQ/ISZERO or TAINT_* above
        bool lhs_tainted;
        bool rhs_tainted;
        uint256_t lhs;
        uint256_t rhs;
        uint256_t expected{};
        bool outcome{};
    };

    inline bool
    eval_compare(uint8_t const kind, uint256_t const &lhs, uint256_t const &rhs)
    {
        switch (kind) {
        case 0x10: // LT
            return lhs < rhs;
        case 0x11: // GT
            return lhs > rhs;
        case 0x12: // SLT
            return slt(lhs, rhs);
        case 0x13: // SGT
            return slt(rhs, lhs);
        case 0x14: // EQ
            return lhs == rhs;
        case 0x15: // ISZERO
            return lhs == 0;
        default:
            return false;
        }
    }

    struct SlotTaintState
    {
        bool revoked{false};
        // registered by the interpreter's sload/sstore wrappers
        uint32_t loads_seen{0};
        uint32_t stores_seen{0};
        // pinged from the host get_storage/set_storage (all engines); any
        // mismatch with the *_seen counters means part of the traffic bypassed
        // the taint machinery (e.g. compiled code) and the slot must stay
        // exact.
        uint32_t loads_total{0};
        uint32_t stores_total{0};
        // cumulative offset vs the transaction-start value, one entry per
        // SSTORE; the last entry is the net delta.
        std::vector<uint256_t> write_offsets{};
        std::vector<TaintConstraint> constraints{};
    };

    // Re-evaluate every recorded comparison with the actual merged base;
    // all outcomes must be unchanged for the delta fix to be sound.
    inline bool
    check_constraints(SlotTaintState const &s, uint256_t const &base)
    {
        for (TaintConstraint const &c : s.constraints) {
            uint256_t const lhs = c.lhs_tainted ? base + c.lhs : c.lhs;
            switch (c.kind) {
            case TAINT_MASK_PASS:
                if ((lhs & ~c.rhs) != 0) {
                    return false;
                }
                break;
            case TAINT_MASK_EXTRACT:
                if ((lhs & c.rhs) != c.expected) {
                    return false;
                }
                break;
            case TAINT_SHR_EXTRACT:
                if ((c.rhs < 256 ? lhs >> c.rhs : uint256_t{0}) != c.expected) {
                    return false;
                }
                break;
            default: {
                uint256_t const rhs = c.rhs_tainted ? base + c.rhs : c.rhs;
                if (eval_compare(c.kind, lhs, rhs) != c.outcome) {
                    return false;
                }
            }
            }
        }
        return true;
    }

    struct TaintNode
    {
        SlotTaintState *slot;
        uint256_t offset;
    };

    class SlotTaintRegistry
    {
        using Key = std::pair<evmc::address, evmc::bytes32>;
        std::map<Key, SlotTaintState> slots_{};
        std::deque<TaintNode> nodes_{};

        SlotTaintState &
        slot(evmc::address const &addr, evmc::bytes32 const &key)
        {
            return slots_[Key{addr, key}];
        }

    public:
        // Interpreter-side registration -----------------------------------

        // Returns a stack tag (0 = untainted) for the value produced by an
        // SLOAD of (addr, key).
        uint32_t on_sload(evmc::address const &addr, evmc::bytes32 const &key)
        {
            auto &s = slot(addr, key);
            ++s.loads_seen;
            if (s.revoked) {
                return 0;
            }
            uint256_t const offset =
                s.write_offsets.empty() ? uint256_t{0} : s.write_offsets.back();
            nodes_.push_back(TaintNode{&s, offset});
            return static_cast<uint32_t>(nodes_.size());
        }

        // Registers an SSTORE of `value_tag`-tagged data to (addr, key).
        // `key_tag` non-zero means the slot key itself was tainted (leak).
        void on_sstore(
            evmc::address const &addr, evmc::bytes32 const &key,
            uint32_t const value_tag, uint32_t const key_tag)
        {
            if (key_tag != 0) {
                revoke(key_tag);
            }
            auto &s = slot(addr, key);
            ++s.stores_seen;
            if (value_tag != 0) {
                TaintNode const &node = nodes_[value_tag - 1];
                if (node.slot == &s && !s.revoked) {
                    s.write_offsets.push_back(node.offset);
                    return;
                }
                // tainted value leaked into a different slot
                node.slot->revoked = true;
            }
            // overwritten with a value not derived from this slot
            s.revoked = true;
        }

        static constexpr size_t MAX_CONSTRAINTS = 256;

        // Records a comparison involving at least one tainted operand.
        // Cross-slot tainted comparisons cannot be validated per-slot and
        // revoke both origins.
        void record_compare(
            uint8_t const kind, uint32_t const tag_lhs, uint256_t const &lhs,
            uint32_t const tag_rhs, uint256_t const &rhs)
        {
            TaintNode const *const nl =
                tag_lhs != 0 ? &nodes_[tag_lhs - 1] : nullptr;
            TaintNode const *const nr =
                tag_rhs != 0 ? &nodes_[tag_rhs - 1] : nullptr;
            if (nl != nullptr && nr != nullptr && nl->slot != nr->slot) {
                nl->slot->revoked = true;
                nr->slot->revoked = true;
                return;
            }
            SlotTaintState *const s = nl != nullptr ? nl->slot : nr->slot;
            if (s->revoked) {
                return;
            }
            if (s->constraints.size() >= MAX_CONSTRAINTS) {
                s->revoked = true;
                return;
            }
            s->constraints.push_back(TaintConstraint{
                kind,
                nl != nullptr,
                nr != nullptr,
                nl != nullptr ? nl->offset : lhs,
                nr != nullptr ? nr->offset : rhs,
                uint256_t{0},
                eval_compare(kind, lhs, rhs)});
        }

        // Records a value-pinned constraint (mask/shift family) on the
        // tainted node's slot.
        void record_value_constraint(
            uint32_t const tag, uint8_t const kind, uint256_t const &operand,
            uint256_t const &expected)
        {
            SlotTaintState *const s = nodes_[tag - 1].slot;
            if (s->revoked) {
                return;
            }
            if (s->constraints.size() >= MAX_CONSTRAINTS) {
                s->revoked = true;
                return;
            }
            s->constraints.push_back(TaintConstraint{
                kind,
                true,
                false,
                nodes_[tag - 1].offset,
                operand,
                expected,
                false});
        }

        void revoke(uint32_t const tag)
        {
            if (tag != 0) {
                nodes_[tag - 1].slot->revoked = true;
            }
        }

        uint256_t const &offset_of(uint32_t const tag) const
        {
            return nodes_[tag - 1].offset;
        }

        SlotTaintState const *node_slot(uint32_t const tag) const
        {
            return nodes_[tag - 1].slot;
        }

        uint32_t derive(uint32_t const tag, uint256_t const &new_offset)
        {
            nodes_.push_back(TaintNode{nodes_[tag - 1].slot, new_offset});
            return static_cast<uint32_t>(nodes_.size());
        }

        // Host-side pings (engine-agnostic coverage counters) --------------

        void note_load(evmc::address const &addr, evmc::bytes32 const &key)
        {
            ++slot(addr, key).loads_total;
        }

        void note_store(evmc::address const &addr, evmc::bytes32 const &key)
        {
            ++slot(addr, key).stores_total;
        }

        // Merge-side query --------------------------------------------------

        // Returns the slot state if every access went through the taint
        // machinery and the slot was never revoked; nullptr otherwise.
        SlotTaintState const *
        valid_delta(evmc::address const &addr, evmc::bytes32 const &key) const
        {
            auto const it = slots_.find(Key{addr, key});
            if (it == slots_.end()) {
                return nullptr;
            }
            SlotTaintState const &s = it->second;
            if (s.revoked || s.write_offsets.empty() ||
                s.loads_seen != s.loads_total ||
                s.stores_seen != s.stores_total) {
                return nullptr;
            }
            return &s;
        }
    };

    // Per-call-frame shadow of the EVM stack: one tag per stack cell plus the
    // pending tag produced by an in-flight SLOAD.
    struct TaintFrame
    {
        SlotTaintRegistry *registry{nullptr};
        uint32_t pending_load{0};
        // Exact count of nonzero tags. Taint exists only on short SLOAD->use
        // chains, so this is 0 for the vast majority of instructions and lets
        // the hooks return immediately; every tag write keeps it exact.
        uint32_t live{0};
        std::array<uint32_t, 1024> tags{};
    };
}
