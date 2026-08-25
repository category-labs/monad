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

// Per-site counters distinguish EVM, trie and witness hashing.
// Enabled by MONAD_ZKVM_KECCAK_SITES; appended after the public block hash.

#pragma once

#include <cstddef>
#include <cstdint>

namespace monad::keccak_sites
{
    enum Site : unsigned
    {
        SHA3_OPCODE = 0,   // EVM KECCAK256 opcode
        READ_ACCT_ADDR,    // partial_trie_db read_account: keccak(addr)
        READ_STOR_ADDR,    // partial_trie_db read_storage: keccak(addr)
        READ_STOR_SLOT,    // partial_trie_db read_storage: keccak(slot)
        COMMIT_ACCT_ADDR,  // commit pass 1: keccak(addr)
        COMMIT_SLOT_PUT,   // commit: keccak(slot), upsert
        COMMIT_SLOT_DEL,   // commit: keccak(slot), erase
        COMMIT_DEL_ADDR,   // commit pass 2: keccak(addr) of a deleted account
        TRIE_PRIME,        // OffsetTrie priming sweep and hash()
        TRIE_ENCODE,       // child_ref_compute / encode_rlp: a node hashed on demand
        CODE_INDEX,        // Bytecode hash for the code index
        BODY_ROOTS,        // body_roots: tx / receipts / withdrawals tries
        HEADER_HASH,       // Block and ancestor header hashes
        // State-access sites count calls only; permutation slots stay zero.
        ACCT_LOOKUP,       // State::current_account_state entered
        ACCT_FIND_MISS,    // ... and current_ missed, so the original_ path ran
        DIRTY_EMPLACE,     // the per-frame dirty-set insert ran
        STOR_LOOKUP,       // State::get_storage entered
        ACCT_MEMO_HIT,     // ... the one-entry memo answered the lookup
        N_SITES
    };

    // Little-endian u32 layout: N_SITES calls, then N_SITES permutation counts.
    // Permutations count work before memoisation, not precompile executions.
    inline std::uint32_t counters[2 * N_SITES]{};

    inline void hit(Site const s, std::size_t const len) noexcept
    {
        ++counters[s];
        // One permutation per full 136-byte block, plus the padded final block.
        counters[N_SITES + s] += static_cast<std::uint32_t>(len / 136 + 1);
    }

    // Count a state access without adding permutation work.
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
