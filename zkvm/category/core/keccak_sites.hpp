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

// Per-site keccak counters, emitted after the public values.
//
// Why this exists rather than reading ziskemu's call-path report: that report groups by the
// innermost frames, its leaf resolves to `Context::exit` on this guest, and it therefore
// attributed 96 % of the block's duplicate hashes to "EVM execution" when in fact the guest's own
// key hashing -- read_account / read_storage, which ARE called from inside execution -- supplies a
// larger share than the SHA3 opcode does. A memo on that opcode reaches only 13 % of the duplicates,
// which is what settles the attribution. Counters at the call sites cannot be misattributed: each one
// is incremented by the line that hashes.
//
// Same method as the JUMPDEST question, which it settled: counters in the public output, roots still
// checked, so a run that reports is also a run that is verified.
//
// Diagnostic only. Enabled by -DMONAD_ZKVM_KECCAK_SITES; absent from any build without it, so the
// shipped guest carries neither the array nor the increments.

#pragma once

// Included only when MONAD_ZKVM_KECCAK_SITES is set (the includers guard it), so no inner #ifdef.

#include <cstddef>
#include <cstdint>

namespace monad::keccak_sites
{
    enum Site : unsigned
    {
        SHA3_OPCODE = 0,   // KECCAK256, the block's own hashing
        READ_ACCT_ADDR,    // partial_trie_db read_account: keccak(addr)
        READ_STOR_ADDR,    // partial_trie_db read_storage: keccak(addr), sroot_ miss
        READ_STOR_SLOT,    // partial_trie_db read_storage: keccak(slot)
        COMMIT_ACCT_ADDR,  // commit pass 1: keccak(addr)
        COMMIT_SLOT_PUT,   // commit: keccak(slot), upsert
        COMMIT_SLOT_DEL,   // commit: keccak(slot), erase
        COMMIT_DEL_ADDR,   // commit pass 2: keccak(addr) of a deleted account
        TRIE_PRIME,        // OffsetTrie ctor: the bottom-up priming sweep
        TRIE_ENCODE,       // child_ref_compute / encode_rlp: a node hashed on demand
        CODE_INDEX,        // ffi: keccak(code) to key the code index
        BODY_ROOTS,        // body_roots: tx / receipts / withdrawals tries
        HEADER_HASH,       // ffi: keccak(header rlp) for the block hash and the ancestor walk
        // State-access sites. Counted only — a permutation count is meaningless here, so
        // their perms slots stay zero. The 256-byte output budget is what caps the list:
        // 96 bytes of roots + 2 * 18 * 4 = 240.
        ACCT_LOOKUP,        // State::current_account_state entered
        ACCT_FIND_MISS,     // ... and the current_ map missed, so the original_ path ran
        DIRTY_EMPLACE,      // the per-frame dirty-set insert ran
        STOR_LOOKUP,        // State::get_storage entered
        ACCT_MEMO_HIT,      // ... the one-entry memo answered the lookup
        POP_REJECT,         // State::pop_reject entered
        POP_ACCEPT,         // State::pop_accept entered
        N_SITES
    };

    // Calls and keccak-f permutations, per site. ZisK prices the permutation, not
    // the call, and a call's input length is unbounded (a 9 kB bytecode is 71
    // permutations), so a call count alone cannot be turned into a cost share.
    // ONE array, not two: it is emitted as a single byte range, and two separate
    // `inline` variables have no guaranteed order or spacing in memory.
    // [0, N_SITES)          call counts
    // [N_SITES, 2*N_SITES)  keccak-f permutations
    // u32, not u64: ZisK's output buffer is 256 bytes and the three roots already
    // take 96, so 2 * N_SITES u64 would not fit. Per-block counts are ~1e5.
    inline std::uint32_t counters[2 * N_SITES]{};

    // Second-slot map for the revert-coverage probe. The state sites have no permutation count,
    // so the slot is free, and the 256-byte output budget has no room for a site each. Read only
    // with the matching decoder -- these pairings are not meaningful anywhere else:
    //
    //   POP_REJECT      count = rejects            slot2 = records replayed
    //   POP_ACCEPT      count = accepts            slot2 = summed frame depth at accept
    //   ACCT_FIND_MISS  count = map misses         slot2 = replayed records that ERASED a row
    //   STOR_LOOKUP     count = get_storage        slot2 = replayed records a child had PROMOTED
    //   ACCT_MEMO_HIT   count = memo hits          slot2 = rejects where the row was destructed
    //   DIRTY_EMPLACE   count = dirty inserts      slot2 = summed frame depth at reject
    //
    // Count a site with no notion of length — the state-access sites.
    inline void bump(Site const s) noexcept
    {
        ++counters[s];
    }

    inline void add2(Site const s, std::size_t const v) noexcept
    {
        counters[N_SITES + s] += static_cast<std::uint32_t>(v);
    }

    inline void hit(Site const s, std::size_t const len) noexcept
    {
        ++counters[s];
        // Sponge rate is 136 B and padding always adds a block.
        counters[N_SITES + s] += static_cast<std::uint32_t>(len / 136 + 1);
    }

    inline unsigned char const *bytes() noexcept
    {
        return reinterpret_cast<unsigned char const *>(counters);
    }

    inline constexpr std::size_t size() noexcept
    {
        return sizeof(counters);
    }
}

#define MONAD_KECCAK_SITE(s, len) ::monad::keccak_sites::hit(::monad::keccak_sites::s, (len))
#define MONAD_GUEST_SITE(s) ::monad::keccak_sites::bump(::monad::keccak_sites::s)
#define MONAD_GUEST_ADD2(s, v) ::monad::keccak_sites::add2(::monad::keccak_sites::s, (v))
