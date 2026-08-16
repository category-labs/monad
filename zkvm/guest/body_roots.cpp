// Copyright (C) 2025-26 Category Labs, Inc.
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

// Ordered-trie root for the block-body binding. Self-contained on purpose:
// the node computes these roots through its database machinery, which the
// guest does not link, and the witness trie code is keyed by offsets rather
// than by free key bytes. Correctness is anchored the only way that matters
// for consensus code — the computed roots are compared against canonical
// mainnet headers on every measured block, and a tampered body must abort.

#include "body_roots.hpp"

#include <category/core/keccak.hpp>

#include <algorithm>
#include <cstddef>
#include <cstdint>

MONAD_NAMESPACE_BEGIN

namespace
{
    // Minimal RLP emission. Local rather than shared with the node's encoders:
    // those work in preallocated spans sized by their callers, while this
    // builder appends — and these five helpers are small enough that clarity
    // beats reuse.
    void append_header(byte_string &out, size_t const n, unsigned char const base)
    {
        if (n < 56) {
            out.push_back(static_cast<unsigned char>(base + n));
            return;
        }
        unsigned char be[8];
        int k = 0;
        for (int i = 7; i >= 0; --i) {
            auto const b = static_cast<unsigned char>((n >> (8 * i)) & 0xff);
            if (k || b) {
                be[k++] = b;
            }
        }
        out.push_back(static_cast<unsigned char>(base + 55 + k));
        out.append(be, static_cast<size_t>(k));
    }

    // Append variants: the callers assemble payloads in place, so the string
    // headers go straight into the destination instead of through temporaries.
    void append_str(byte_string &out, byte_string_view const v)
    {
        if (v.size() == 1 && v[0] < 0x80) {
            out.push_back(v[0]);
            return;
        }
        append_header(out, v.size(), 0x80);
        out.append(v);
    }

    byte_string rlp_list(byte_string_view const payload)
    {
        byte_string out;
        out.reserve(payload.size() + 9);
        append_header(out, payload.size(), 0xc0);
        out.append(payload);
        return out;
    }

    // Hex-prefix encoding of nibbles [from, to), yellow paper appendix C.
    byte_string
    hex_prefix(std::vector<uint8_t> const &nib, size_t from, size_t const to,
               bool const leaf)
    {
        byte_string s;
        uint8_t const flag = leaf ? 2 : 0;
        if ((to - from) % 2) {
            s.push_back(static_cast<unsigned char>(((flag | 1) << 4) | nib[from]));
            ++from;
        }
        else {
            s.push_back(static_cast<unsigned char>(flag << 4));
        }
        for (; from < to; from += 2) {
            s.push_back(static_cast<unsigned char>((nib[from] << 4) | nib[from + 1]));
        }
        return s;
    }

    struct Item
    {
        std::vector<uint8_t> nib; // key, as nibbles
        byte_string_view val;
    };

    // A child inside a parent node: embedded verbatim when its RLP is short,
    // else the RLP string of its keccak.
    byte_string child_ref(byte_string const &child)
    {
        if (child.size() < 32) {
            return child;
        }
        auto const h = to_bytes(keccak256(child));
        byte_string out;
        out.reserve(33);
        append_str(out, byte_string_view{h.bytes, 32});
        return out;
    }

    // RLP of the node covering items [lo, hi) — sorted by nibble sequence —
    // at nibble depth d. RLP-encoded integer keys are prefix-free, so no key
    // ever terminates inside another's path and branch value slots stay empty;
    // the recursion relies on that.
    byte_string
    node_rlp(std::vector<Item> const &it, size_t const lo, size_t const hi,
             size_t const d)
    {
        if (hi - lo == 1) {
            byte_string payload;
            payload.reserve(it[lo].nib.size() / 2 + it[lo].val.size() + 12);
            append_str(payload, hex_prefix(it[lo].nib, d, it[lo].nib.size(), true));
            append_str(payload, it[lo].val);
            return rlp_list(payload);
        }
        // Longest nibble prefix shared by the whole range -> extension node.
        size_t p = d;
        for (;; ++p) {
            uint8_t const c = it[lo].nib[p];
            bool same = true;
            for (size_t k = lo + 1; k < hi; ++k) {
                if (p >= it[k].nib.size() || it[k].nib[p] != c) {
                    same = false;
                    break;
                }
            }
            if (!same) {
                break;
            }
        }
        if (p > d) {
            byte_string payload;
            append_str(payload, hex_prefix(it[lo].nib, d, p, false));
            payload += child_ref(node_rlp(it, lo, hi, p));
            return rlp_list(payload);
        }
        byte_string payload;
        payload.reserve(17 * 33 + 4);
        size_t k = lo;
        for (uint8_t nb = 0; nb < 16; ++nb) {
            size_t const start = k;
            while (k < hi && it[k].nib[d] == nb) {
                ++k;
            }
            if (k == start) {
                payload.push_back(0x80); // empty child slot
            }
            else {
                payload += child_ref(node_rlp(it, start, k, d + 1));
            }
        }
        payload.push_back(0x80); // value slot: empty (keys are prefix-free)
        return rlp_list(payload);
    }
}

bytes32_t ordered_trie_root(std::vector<byte_string> const &items)
{
    std::vector<byte_string_view> views;
    views.reserve(items.size());
    for (auto const &i : items) {
        views.emplace_back(i);
    }
    return ordered_trie_root(std::span<byte_string_view const>{views});
}

bytes32_t ordered_trie_root(std::span<byte_string_view const> const items)
{
    if (items.empty()) {
        return NULL_ROOT;
    }
    std::vector<Item> it;
    it.reserve(items.size());
    for (size_t i = 0; i < items.size(); ++i) {
        // key = rlp(i): 0 -> 0x80, 1..127 -> the byte itself, else
        // 0x80+len || big-endian(i)
        byte_string key;
        if (i == 0) {
            key.push_back(0x80);
        }
        else if (i < 128) {
            key.push_back(static_cast<unsigned char>(i));
        }
        else {
            unsigned char be[8];
            int k = 0;
            for (int b = 7; b >= 0; --b) {
                auto const byte = static_cast<unsigned char>((i >> (8 * b)) & 0xff);
                if (k || byte) {
                    be[k++] = byte;
                }
            }
            key.push_back(static_cast<unsigned char>(0x80 + k));
            key.append(be, static_cast<size_t>(k));
        }
        Item item;
        item.nib.reserve(key.size() * 2);
        for (unsigned char const b : key) {
            item.nib.push_back(b >> 4);
            item.nib.push_back(b & 0xf);
        }
        item.val = items[i];
        it.push_back(std::move(item));
    }
    std::sort(it.begin(), it.end(), [](Item const &a, Item const &b) {
        return a.nib < b.nib;
    });
    byte_string const root = node_rlp(it, 0, it.size(), 0);
    return to_bytes(keccak256(root));
}

MONAD_NAMESPACE_END
