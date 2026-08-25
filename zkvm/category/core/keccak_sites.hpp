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

// Diagnostic Keccak counters, appended after the public block hash.
// Counting at call sites distinguishes EVM hashing from trie and witness work
// that the emulator's call-path report groups together.
// Includers enable this header only with MONAD_ZKVM_KECCAK_SITES.

#pragma once

#include <cstddef>
#include <cstdint>

namespace monad::keccak_sites
{
    enum Site : unsigned
    {
        SHA3_OPCODE = 0,   // EVM KECCAK256 opcode
        READ_ACCT_ADDR,    // partial_trie_db read_account: keccak(addr)
        READ_STOR_ADDR,    // partial_trie_db read_storage: keccak(addr), sroot_ miss
        READ_STOR_SLOT,    // partial_trie_db read_storage: keccak(slot)
        COMMIT_ACCT_ADDR,  // commit pass 1: keccak(addr)
        COMMIT_SLOT_PUT,   // commit: keccak(slot), upsert
        COMMIT_SLOT_DEL,   // commit: keccak(slot), erase
        COMMIT_DEL_ADDR,   // commit pass 2: keccak(addr) of a deleted account
        TRIE_PRIME,        // OffsetTrie priming sweep and hash()
        TRIE_ENCODE,       // child_ref_compute / encode_rlp: a node hashed on demand
        CODE_INDEX,        // ffi: keccak(code) to key the code index
        BODY_ROOTS,        // body_roots: tx / receipts / withdrawals tries
        HEADER_HASH,       // Block and ancestor header hashes
        // State-access sites. Counted only -- a permutation count is meaningless
        // here, so their perms slots stay zero. The 256-byte output budget caps
        // the list: 96 bytes of roots + 2 * 18 * 4 = 240.
        ACCT_LOOKUP,       // State::current_account_state entered
        ACCT_FIND_MISS,    // ... and current_ missed, so the original_ path ran
        DIRTY_EMPLACE,     // the per-frame dirty-set insert ran
        STOR_LOOKUP,       // State::get_storage entered
        ACCT_MEMO_HIT,     // ... the one-entry memo answered the lookup
        N_SITES
    };

    // Calls occupy [0, N_SITES); permutations occupy [N_SITES, 2*N_SITES).
    // Permutation counts account for differing input lengths.
    // One contiguous u32 array keeps the diagnostic output compact.
    inline std::uint32_t counters[2 * N_SITES]{};

    inline void hit(Site const s, std::size_t const len) noexcept
    {
        ++counters[s];
        // One permutation per full 136-byte block, plus the padded final block.
        counters[N_SITES + s] += static_cast<std::uint32_t>(len / 136 + 1);
    }

    // Count a site with no notion of length -- the state-access sites.
    inline void bump(Site const s) noexcept
    {
        ++counters[s];
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
