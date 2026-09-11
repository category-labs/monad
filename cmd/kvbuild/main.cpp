// Standalone KV-DB bulk-build utility (prototype).
//
// Subcommands:
//   build  <snapshot_dir> <block> <out_image> [flat|pages]
//       Ingest a filesystem snapshot and bottom-up bulk-pack a fixed-4KB
//       B+tree image (+ .kvhdr sidecar). One-shot fresh-state build (NOT the
//       per-block commit-merge): no refcounts, no COW sharing.
//       Storage-leaf format: `pages` (MIP-8 sparse pages, default) or `flat`
//       (one {slot,value} per record). Both selectable so we can compare.
//   verify <snapshot_dir> <block> <image>
//       Load the image (mmap + kv_header) as a fresh reader and check that
//       EVERY account and slot in the snapshot round-trips. Correctness gate:
//       persisted bytes vs the snapshot oracle, in a separate process.
//   pagestats <snapshot_dir> <block>
//       Report the MIP-8 page popcount distribution (no build).
//
// Child links are flat 64-bit byte offsets into the image (node_ref); they are
// position-independent -- resolve(ref) = mmap_base + ref here, and becomes
// chunk arithmetic (base K) when loaded onto /dev/triedb. NOTE: mmap is used
// ONLY by this offline tool; real execution reads go through io_uring + the
// fiber handoff, never mmap.
//
// KV image layout (all nodes fixed 4096B). Non-extension nodes have an 8B
// header: [0]=type [1]=key_len [2..3]=count(u16) [4..7]=pad.
//   INTERNAL           : count x { key[key_len], node_ref(8) } (key=child min)
//   LEAF_ACCOUNT       : count x { address(20), account(80), storage_ref(8) }
//   LEAF_STORAGE_FLAT  : count x { slot(32), value(32) }
//   LEAF_STORAGE_PAGE  : header, then uint16 offset directory[count], then
//                        packed page records; each record =
//                          page_base(32) bitmap(16) flag(1)
//                          + inline value(32)*popcount   (flag==0), or
//                          + ext_ref(8)                  (flag==1)
//   STORAGE_EXT        : headerless; raw value(32)*popcount (<=4096). Reached
//                        only via a page record's ext_ref, for pages that are
//                        too full (>=127 of 128 slots) to fit inline.
//
// Snapshot layout (from db_snapshot_filesystem.cpp / db_snapshot.cpp):
//   <dir>/<block>/<shard>/account : sequence of RLP account entries.
//   <dir>/<block>/<shard>/storage : sequence of [uint64 account_offset]
//                                   [RLP(slot,val)] entries.

#include <category/async/storage_pool.hpp>
#include <category/core/address.hpp>
#include <category/core/assert.h>
#include <category/core/byte_string.hpp>
#include <category/core/bytes.hpp>
#include <category/core/keccak.hpp>
#include <category/execution/ethereum/core/account.hpp>
#include <category/execution/ethereum/db/util.hpp>

#include <map>

#include <algorithm>
#include <array>
#include <cstdint>
#include <cstdio>
#include <cstring>
#include <filesystem>
#include <optional>
#include <span>
#include <string>
#include <unordered_map>
#include <vector>

#include <fcntl.h>
#include <sys/mman.h>
#include <unistd.h>

using namespace monad;

namespace
{
    // ── Node format constants ───────────────────────────────────────────
    constexpr size_t NODE_SIZE = 4096;
    constexpr size_t HDR = 8;
    constexpr uint64_t NULL_REF = ~uint64_t{0};

    enum NodeType : uint8_t
    {
        N_INTERNAL = 0,
        N_LEAF_ACCOUNT = 1,
        N_LEAF_STORAGE_FLAT = 2,
        N_LEAF_STORAGE_PAGE = 3,
        N_BLOCKMAP_INTERNAL = 5, // block map B+tree internal node
        N_BLOCKMAP_LEAF = 6, // block map B+tree leaf
        N_CODE_INLINE = 7, // code root page holding the whole code
        N_CODE_INDEX = 8, // code root page pointing to raw data pages
        // extension nodes are headerless; no type byte
    };

    // block map B+tree page layout (must match trie_db.cpp's kv::blockmap).
    // Header {type, key_len, val_len, count}; leaf: count entries of
    // key_len+val_len; internal: count child refs (8B) then count-1 separators.
    constexpr size_t BP_TYPE = 0, BP_KEYLEN = 1, BP_VALLEN = 2, BP_COUNT = 4,
                     BP_HDR = 8;
    // key=(block 8, id 32); val=(block_root 8, parent 32, block_hash 32).
    // Must match trie_db.cpp's kv::blockmap. (block_root = state root when the
    // block has no blobs, as in the base image.)
    constexpr size_t BM_KL = 40, BM_VL = 72;
    // code page layout (must match trie_db.cpp): root page [0]=type, [8]=len u64;
    // inline code at 16, or index: nchild u32 at 16, child refs u64[] at 24.
    constexpr size_t CODE_LEN = 8, CODE_NCHILD = 16, CODE_CHILDREN = 24,
                     CODE_INLINE_OFF = 16;

    constexpr size_t ACCT_KEY = 20; // address
    constexpr size_t STOR_KEY = 32; // slot / page_base
    constexpr size_t ACCT_REC = ACCT_KEY + sizeof(Account) + 8; // 108
    constexpr size_t STOR_REC_FLAT = 32 + 32; // 64

    // page record field offsets
    constexpr size_t PG_BASE = 0; // 32
    constexpr size_t PG_BITMAP = 32; // 16
    constexpr size_t PG_FLAG = 48; // 1
    constexpr size_t PG_PAYLOAD = 49; // inline values, or 8B ext_ref
    constexpr size_t PG_STUB_SIZE = PG_PAYLOAD + 8; // 57 (extension record)
    // A page with popcount p stored inline costs PG_PAYLOAD + 32*p, plus a 2B
    // directory entry. It fits a leaf alone iff HDR+2+PG_PAYLOAD+32*p<=NODE.
    // => p <= 126. Pages with p>=127 must use an extension node.
    constexpr size_t PG_INLINE_MAX_POPCOUNT = 126;

    // ── device mode (kvdb_base: KV owns the device tail as flat 4KB pages) ─
    // KV writes its nodes directly to [base_offset, end) via its own fd (no
    // storage_pool, no chunks), where base_offset = phys(seq chunk
    // KVDB_FIRST_SEQ_CHUNK); triedb keeps the whole device but is kept below
    // that boundary by the category/mpt/trie.cpp allocation guard.

    inline bool is_device_target(char const *const p)
    {
        return std::strncmp(p, "/dev/", 5) == 0;
    }

    // ── bit helpers over a 128-bit little-endian bitmap ─────────────────
    inline void bit_set(unsigned char *const bm, size_t const idx)
    {
        bm[idx >> 3] =
            static_cast<unsigned char>(bm[idx >> 3] | (1u << (idx & 7)));
    }

    inline bool bit_test(unsigned char const *const bm, size_t const idx)
    {
        return (bm[idx >> 3] >> (idx & 7)) & 1u;
    }

    // number of set bits in positions [0, idx)
    inline size_t bit_rank(unsigned char const *const bm, size_t const idx)
    {
        size_t const full = idx >> 3;
        size_t const rem = idx & 7;
        size_t r = 0;
        for (size_t b = 0; b < full; ++b) {
            r += static_cast<size_t>(__builtin_popcount(bm[b]));
        }
        if (rem) {
            r += static_cast<size_t>(
                __builtin_popcount(bm[full] & ((1u << rem) - 1)));
        }
        return r;
    }

    // page_base = slot with the low 7 bits cleared; idx = the low 7 bits.
    inline bytes32_t page_base_of(bytes32_t const &slot)
    {
        bytes32_t b = slot;
        b.bytes[31] = static_cast<unsigned char>(b.bytes[31] & 0x80);
        return b;
    }

    inline size_t page_idx_of(bytes32_t const &slot)
    {
        return static_cast<size_t>(slot.bytes[31] & 0x7f);
    }

    // ── mmap helper ─────────────────────────────────────────────────────
    struct Mapped
    {
        int fd{-1};
        unsigned char const *data{nullptr};
        size_t len{0};
    };

    Mapped map_file(std::filesystem::path const &p, bool const require = false)
    {
        Mapped m;
        if (!std::filesystem::is_regular_file(p)) {
            MONAD_ASSERT(!require);
            return m;
        }
        m.fd = ::open(p.c_str(), O_RDONLY);
        MONAD_ASSERT(m.fd != -1);
        m.len = std::filesystem::file_size(p);
        if (m.len) {
            void *const d =
                ::mmap(nullptr, m.len, PROT_READ, MAP_SHARED, m.fd, 0);
            MONAD_ASSERT(d != MAP_FAILED);
            m.data = static_cast<unsigned char const *>(d);
        }
        return m;
    }

    void unmap(Mapped &m)
    {
        if (m.data) {
            ::munmap(const_cast<unsigned char *>(m.data), m.len);
        }
        if (m.fd != -1) {
            ::close(m.fd);
        }
    }

    // ── Ingest buffers ──────────────────────────────────────────────────
    struct AcctIn
    {
        Address addr;
        Account acct;
    };

    struct StorIn
    {
        uint32_t acct; // index into accounts (read order)
        bytes32_t slot;
        bytes32_t val;
    };

    uint64_t ingest(
        std::filesystem::path const &root, std::vector<AcctIn> &accounts,
        std::vector<StorIn> &storage,
        std::map<bytes32_t, byte_string> &codes)
    {
        uint64_t shards = 0;
        for (auto const &dir : std::filesystem::directory_iterator{root}) {
            if (!dir.is_directory()) {
                continue;
            }
            ++shards;
            Mapped acc = map_file(dir.path() / "account");
            Mapped sto = map_file(dir.path() / "storage");
            if (acc.data) {
                ::madvise(
                    const_cast<unsigned char *>(acc.data),
                    acc.len,
                    MADV_SEQUENTIAL);
            }
            if (sto.data) {
                ::madvise(
                    const_cast<unsigned char *>(sto.data),
                    sto.len,
                    MADV_SEQUENTIAL);
            }

            std::unordered_map<uint64_t, uint32_t> offset_to_idx;
            {
                byte_string_view v{acc.data, acc.len};
                while (!v.empty()) {
                    uint64_t const off = acc.len - v.size();
                    auto res = decode_account_db(v);
                    MONAD_ASSERT(res.has_value());
                    offset_to_idx.emplace(
                        off, static_cast<uint32_t>(accounts.size()));
                    accounts.push_back(
                        {res.value().first, res.value().second});
                }
            }
            {
                byte_string_view v{sto.data, sto.len};
                while (!v.empty()) {
                    uint64_t account_offset = 0;
                    std::memcpy(
                        &account_offset, v.data(), sizeof(account_offset));
                    v.remove_prefix(sizeof(account_offset));
                    auto res = decode_storage_db_raw(v);
                    MONAD_ASSERT(res.has_value());
                    auto const it = offset_to_idx.find(account_offset);
                    MONAD_ASSERT(it != offset_to_idx.end());
                    storage.push_back(
                        {it->second,
                         to_bytes(res.value().first),
                         to_bytes(res.value().second)});
                }
            }
            // code: sequence of [uint64 len][len bytes]. The hash is not stored
            // (code is content-addressed), so recompute code_hash = keccak256.
            Mapped cod = map_file(dir.path() / "code");
            if (cod.data) {
                byte_string_view v{cod.data, cod.len};
                while (!v.empty()) {
                    uint64_t len = 0;
                    std::memcpy(&len, v.data(), sizeof(len));
                    v.remove_prefix(sizeof(len));
                    MONAD_ASSERT(v.size() >= len);
                    bytes32_t const h =
                        to_bytes(keccak256(byte_string_view{v.data(), len}));
                    codes.emplace(h, byte_string{v.data(), len});
                    v.remove_prefix(len);
                }
            }
            unmap(cod);
            unmap(sto);
            unmap(acc);
        }
        return shards;
    }

    // ── Node readers (shared by build self-check and verify) ────────────
    // kvdb_base: KV is a FLAT array of 4KB pages, so a logical node_ref is just
    // a byte offset from the image base (base + ref) for both file mode (base =
    // mmap at offset 0) and device mode (base = mmap at base_offset).
    struct Resolver
    {
        unsigned char const *base{nullptr};

        unsigned char const *operator()(uint64_t const ref) const
        {
            return base + ref;
        }
    };

    // Follow internal nodes to the leaf whose range contains `key`. Works for
    // page storage leaves too: internal separators are leaf-first-keys, so
    // descending with the full slot lands on the leaf holding its page_base.
    uint64_t descend_to_leaf(
        Resolver const &R, uint64_t root, unsigned char const *key,
        size_t const key_len)
    {
        uint64_t ref = root;
        for (;;) {
            unsigned char const *n = R(ref);
            if (n[0] != N_INTERNAL) {
                return ref;
            }
            size_t const kl = n[1];
            uint16_t count;
            std::memcpy(&count, n + 2, sizeof(count));
            unsigned char const *p = n + HDR;
            size_t const esz = kl + 8;
            long chosen = -1;
            for (size_t i = 0; i < count; ++i) {
                if (std::memcmp(p + i * esz, key, kl) <= 0) {
                    chosen = static_cast<long>(i);
                }
                else {
                    break;
                }
            }
            MONAD_ASSERT(chosen >= 0);
            (void)key_len;
            std::memcpy(
                &ref, p + static_cast<size_t>(chosen) * esz + kl, sizeof(ref));
        }
    }

    // Account record (108B) for `addr`, or nullptr.
    unsigned char const *find_account_rec(
        Resolver const &R, uint64_t root, Address const &addr)
    {
        uint64_t const ref = descend_to_leaf(R, root, addr.bytes, ACCT_KEY);
        unsigned char const *n = R(ref);
        MONAD_ASSERT(n[0] == N_LEAF_ACCOUNT);
        uint16_t count;
        std::memcpy(&count, n + 2, sizeof(count));
        unsigned char const *p = n + HDR;
        for (size_t i = 0; i < count; ++i) {
            unsigned char const *rec = p + i * ACCT_REC;
            if (std::memcmp(rec, addr.bytes, 20) == 0) {
                return rec;
            }
        }
        return nullptr;
    }

    // Value (32B) for `slot` in the storage subtree rooted at `sroot`, or
    // nullptr if absent. Handles both flat and page leaf formats.
    unsigned char const *find_slot_value(
        Resolver const &R, uint64_t sroot, bytes32_t const &slot)
    {
        uint64_t const ref = descend_to_leaf(R, sroot, slot.bytes, STOR_KEY);
        unsigned char const *n = R(ref);
        uint16_t count;
        std::memcpy(&count, n + 2, sizeof(count));
        unsigned char const *p = n + HDR;
        if (n[0] == N_LEAF_STORAGE_FLAT) {
            for (size_t i = 0; i < count; ++i) {
                unsigned char const *rec = p + i * STOR_REC_FLAT;
                if (std::memcmp(rec, slot.bytes, 32) == 0) {
                    return rec + 32;
                }
            }
            return nullptr;
        }
        MONAD_ASSERT(n[0] == N_LEAF_STORAGE_PAGE);
        bytes32_t const base_key = page_base_of(slot);
        size_t const idx = page_idx_of(slot);
        // directory of uint16 offsets, records sorted by page_base
        for (size_t i = 0; i < count; ++i) {
            uint16_t off;
            std::memcpy(&off, p + i * 2, sizeof(off));
            unsigned char const *rec = n + off;
            if (std::memcmp(rec + PG_BASE, base_key.bytes, 32) != 0) {
                continue;
            }
            unsigned char const *bm = rec + PG_BITMAP;
            if (!bit_test(bm, idx)) {
                return nullptr; // slot not present in page
            }
            size_t const rank = bit_rank(bm, idx);
            if (rec[PG_FLAG] == 0) {
                return rec + PG_PAYLOAD + rank * 32;
            }
            uint64_t ext_ref;
            std::memcpy(&ext_ref, rec + PG_PAYLOAD, sizeof(ext_ref));
            return R(ext_ref) + rank * 32;
        }
        return nullptr; // page not present
    }

    // ── device read: one flat read-only mmap of KV's image range ────────
    // kvdb_base: KV's image is a contiguous flat range on the device at
    // [base_offset, base_offset + image_bytes). Offline tool only (mmap); real
    // execution reads go through KV's own fd (kv_fd_).
    inline unsigned char const *map_kv_image_dev(
        int const fd, uint64_t const base_offset, uint64_t const image_bytes)
    {
        void *const m = ::mmap(
            nullptr,
            image_bytes,
            PROT_READ,
            MAP_SHARED,
            fd,
            static_cast<off_t>(base_offset));
        MONAD_ASSERT(m != MAP_FAILED);
        return static_cast<unsigned char const *>(m);
    }

    // ── KV header sidecar ───────────────────────────────────────────────
    struct KvHeader
    {
        uint64_t magic;
        uint32_t version;
        uint32_t node_size;
        uint64_t root_ref;
        uint64_t node_count;
        uint64_t image_bytes;
        uint64_t num_accounts;
        uint64_t num_slots;
        uint32_t storage_format; // 0=flat, 1=pages
        uint32_t pad;
        uint64_t ext_nodes;
        // kvdb_base: device byte offset of node_ref 0 = phys(seq chunk
        // KVDB_FIRST_SEQ_CHUNK) for a device, 0 for a file. Read by trie_db's
        // KvShadow. (Layout MUST match trie_db.cpp's kv::KvHeader.)
        uint64_t base_offset;
    };
    constexpr uint64_t KV_MAGIC = 0x314256'4b'2d64766bULL;

    // kvdb_base multiversion: on-device metadata region at the FRONT of KV's
    // range ([base_offset, base_offset + KVDB_META_BYTES)). Header on page 0,
    // then a ring of KVDB_HISTORY_N block roots starting on page 1. A read at
    // block K resolves ring[K % history_n] when lower_bound <= K <= latest.
    // (Layout MUST match trie_db.cpp's kv::KvMeta.)
    struct KvMeta
    {
        uint64_t magic; // KV_META_MAGIC
        uint32_t version; // 7 (v7: adds tx-hash / block-hash index roots)
        uint32_t node_size; // == NODE_SIZE (sanity)
        uint64_t tree_root; // block map root ref
        uint64_t code_tree_root; // code index B+tree root (grow-only)
        uint64_t txhash_index_root; // global tx_hash -> (block,tx_index)
        uint64_t blockhash_index_root; // global block_hash -> number
        uint64_t finalized_block; // finalized tip block
        uint64_t oldest_block; // oldest finalized block still retained
        unsigned char finalized_id[32]; // finalized tip id
        // Consensus commit-state cursors (see trie_db.cpp KvMeta). block ==
        // UINT64_MAX until consensus first stamps it.
        uint64_t proposed_block; // latest proposed (canonical head)
        unsigned char proposed_id[32];
        uint64_t voted_block; // latest voted (safe)
        unsigned char voted_id[32];
    };
    constexpr uint64_t KV_META_MAGIC = 0x31564d'4b'2d64766bULL; // "kvd-KMV1"
    static_assert(sizeof(KvMeta) <= NODE_SIZE);

    // Write the initial metadata region for a fresh build at `block`: the ring
    // holds a single root (this block's), the window is [block, block].
    inline void write_kv_meta(
        int const fd, uint64_t const base_offset, uint64_t const block,
        uint64_t const tree_root, uint64_t const code_tree_root,
        uint64_t const txhash_index_root, uint64_t const blockhash_index_root)
    {
        std::vector<unsigned char> buf(KVDB_META_BYTES, 0);
        KvMeta m{};
        m.magic = KV_META_MAGIC;
        m.version = 7; // v7: adds tx-hash / block-hash index roots
        m.node_size = NODE_SIZE;
        m.tree_root = tree_root;
        m.code_tree_root = code_tree_root;
        m.txhash_index_root = txhash_index_root;
        m.blockhash_index_root = blockhash_index_root;
        m.finalized_block = block;
        m.oldest_block = block;
        // finalized_id left zero; the finalized-tip match is by block number.
        // No proposed/voted cursor yet; consensus stamps them at runtime.
        m.proposed_block = ~uint64_t{0};
        m.voted_block = ~uint64_t{0};
        std::memcpy(buf.data(), &m, sizeof(m));
        ssize_t const wr = ::pwrite(
            fd, buf.data(), buf.size(), static_cast<off_t>(base_offset));
        MONAD_ASSERT(wr == static_cast<ssize_t>(buf.size()));
    }

    // ── Image writer (fixed 4KB nodes, append cursor) ───────────────────
    struct Writer
    {
        // kvdb_base: KV is a FLAT array of 4KB pages written directly to `fd`
        // (no storage_pool, no chunks). A logical node_ref maps to the absolute
        // device byte offset base_offset + ref; base_offset is phys(seq chunk
        // KVDB_FIRST_SEQ_CHUNK) for a device target and 0 for a plain-file image.
        int fd{-1};
        uint64_t base_offset{0};
        uint64_t off{0}; // logical byte offset in node_ref space (base 0)
        uint64_t nodes{0};

        uint64_t emit(unsigned char const *const buf)
        {
            uint64_t const ref = off;
            ssize_t const wr = ::pwrite(
                fd, buf, NODE_SIZE, static_cast<off_t>(base_offset + off));
            MONAD_ASSERT(wr == static_cast<ssize_t>(NODE_SIZE));
            off += NODE_SIZE;
            ++nodes;
            return ref;
        }
    };

    struct LevelEnt
    {
        unsigned char key[STOR_KEY]; // uses key_len bytes
        uint64_t ref;
    };

    uint64_t
    pack_internal(Writer &w, std::vector<LevelEnt> &ents, size_t const key_len)
    {
        size_t const esz = key_len + 8;
        size_t const cap = (NODE_SIZE - HDR) / esz;
        while (ents.size() > 1) {
            std::vector<LevelEnt> up;
            up.reserve(ents.size() / cap + 1);
            size_t i = 0;
            while (i < ents.size()) {
                size_t const count = std::min(cap, ents.size() - i);
                unsigned char buf[NODE_SIZE];
                std::memset(buf, 0, NODE_SIZE);
                buf[0] = N_INTERNAL;
                buf[1] = static_cast<unsigned char>(key_len);
                uint16_t const c = static_cast<uint16_t>(count);
                std::memcpy(buf + 2, &c, sizeof(c));
                unsigned char *q = buf + HDR;
                for (size_t j = 0; j < count; ++j) {
                    std::memcpy(q, ents[i + j].key, key_len);
                    q += key_len;
                    std::memcpy(q, &ents[i + j].ref, 8);
                    q += 8;
                }
                LevelEnt e;
                std::memcpy(e.key, ents[i].key, key_len);
                e.ref = w.emit(buf);
                up.push_back(e);
                i += count;
            }
            ents.swap(up);
        }
        return ents[0].ref;
    }

    // ── flat storage leaves ─────────────────────────────────────────────
    uint64_t pack_storage_flat(
        Writer &w, std::vector<StorIn> const &s, size_t const lo,
        size_t const hi)
    {
        if (lo == hi) {
            return NULL_REF;
        }
        constexpr size_t cap = (NODE_SIZE - HDR) / STOR_REC_FLAT; // 63
        std::vector<LevelEnt> ents;
        ents.reserve((hi - lo) / cap + 1);
        size_t i = lo;
        while (i < hi) {
            size_t const count = std::min(cap, hi - i);
            unsigned char buf[NODE_SIZE];
            std::memset(buf, 0, NODE_SIZE);
            buf[0] = N_LEAF_STORAGE_FLAT;
            buf[1] = static_cast<unsigned char>(STOR_KEY);
            uint16_t const c = static_cast<uint16_t>(count);
            std::memcpy(buf + 2, &c, sizeof(c));
            unsigned char *q = buf + HDR;
            for (size_t j = 0; j < count; ++j) {
                std::memcpy(q, s[i + j].slot.bytes, 32);
                q += 32;
                std::memcpy(q, s[i + j].val.bytes, 32);
                q += 32;
            }
            LevelEnt e;
            std::memcpy(e.key, s[i].slot.bytes, STOR_KEY);
            e.ref = w.emit(buf);
            ents.push_back(e);
            i += count;
        }
        return pack_internal(w, ents, STOR_KEY);
    }

    // ── MIP-8 page storage leaves ───────────────────────────────────────
    // Accumulates variable-size page records, flushing a 4KB slotted leaf when
    // the next record would not fit.
    struct PageLeafBuilder
    {
        Writer &w;
        std::vector<LevelEnt> ents;
        unsigned char scratch[NODE_SIZE]; // packed record bytes for cur leaf
        std::vector<uint16_t> sizes; // per-record size, in add order
        size_t used{0}; // bytes in scratch
        unsigned char first_key[STOR_KEY];

        explicit PageLeafBuilder(Writer &writer)
            : w{writer}
        {
        }

        void flush()
        {
            if (sizes.empty()) {
                return;
            }
            size_t const count = sizes.size();
            unsigned char buf[NODE_SIZE];
            std::memset(buf, 0, NODE_SIZE);
            buf[0] = N_LEAF_STORAGE_PAGE;
            buf[1] = static_cast<unsigned char>(STOR_KEY);
            uint16_t const c = static_cast<uint16_t>(count);
            std::memcpy(buf + 2, &c, sizeof(c));
            size_t const recbase = HDR + count * 2;
            size_t o = recbase;
            size_t scratch_off = 0;
            for (size_t i = 0; i < count; ++i) {
                uint16_t const off = static_cast<uint16_t>(o);
                std::memcpy(buf + HDR + i * 2, &off, sizeof(off));
                std::memcpy(buf + o, scratch + scratch_off, sizes[i]);
                o += sizes[i];
                scratch_off += sizes[i];
            }
            MONAD_ASSERT(o <= NODE_SIZE);
            LevelEnt e;
            std::memcpy(e.key, first_key, STOR_KEY);
            e.ref = w.emit(buf);
            ents.push_back(e);
            sizes.clear();
            used = 0;
        }

        void add(
            unsigned char const *const rec, size_t const size,
            unsigned char const *const page_base)
        {
            size_t const need = HDR + (sizes.size() + 1) * 2 + used + size;
            if (!sizes.empty() && need > NODE_SIZE) {
                flush();
            }
            if (sizes.empty()) {
                std::memcpy(first_key, page_base, STOR_KEY);
            }
            std::memcpy(scratch + used, rec, size);
            used += size;
            sizes.push_back(static_cast<uint16_t>(size));
        }
    };

    uint64_t pack_storage_pages(
        Writer &w, std::vector<StorIn> const &s, size_t const lo,
        size_t const hi, uint64_t &ext_nodes)
    {
        if (lo == hi) {
            return NULL_REF;
        }
        PageLeafBuilder lb{w};
        size_t i = lo;
        while (i < hi) {
            bytes32_t const base_key = page_base_of(s[i].slot);
            size_t const a = i;
            while (i < hi &&
                   std::memcmp(
                       page_base_of(s[i].slot).bytes, base_key.bytes, 32) ==
                       0) {
                ++i;
            }
            size_t const pc = i - a; // distinct idx per slot => popcount
            unsigned char rec[NODE_SIZE];
            std::memcpy(rec + PG_BASE, base_key.bytes, 32);
            unsigned char *const bm = rec + PG_BITMAP;
            std::memset(bm, 0, 16);
            for (size_t r = 0; r < pc; ++r) {
                bit_set(bm, page_idx_of(s[a + r].slot));
            }
            size_t rsize;
            if (pc > PG_INLINE_MAX_POPCOUNT) {
                // extension: values in a dedicated headerless node
                unsigned char ext[NODE_SIZE];
                std::memset(ext, 0, NODE_SIZE);
                for (size_t r = 0; r < pc; ++r) {
                    std::memcpy(ext + r * 32, s[a + r].val.bytes, 32);
                }
                uint64_t const ext_ref = w.emit(ext);
                ++ext_nodes;
                rec[PG_FLAG] = 1;
                std::memcpy(rec + PG_PAYLOAD, &ext_ref, 8);
                rsize = PG_STUB_SIZE;
            }
            else {
                rec[PG_FLAG] = 0;
                for (size_t r = 0; r < pc; ++r) {
                    std::memcpy(rec + PG_PAYLOAD + r * 32, s[a + r].val.bytes, 32);
                }
                rsize = PG_PAYLOAD + 32 * pc;
            }
            lb.add(rec, rsize, base_key.bytes);
        }
        lb.flush();
        return pack_internal(w, lb.ents, STOR_KEY);
    }

    // ── account tree ────────────────────────────────────────────────────
    struct AcctRec
    {
        Address addr;
        Account acct;
        uint64_t sref;
    };

    uint64_t pack_account_tree(Writer &w, std::vector<AcctRec> const &recs)
    {
        MONAD_ASSERT(!recs.empty());
        constexpr size_t cap = (NODE_SIZE - HDR) / ACCT_REC; // 37
        std::vector<LevelEnt> ents;
        ents.reserve(recs.size() / cap + 1);
        size_t i = 0;
        while (i < recs.size()) {
            size_t const count = std::min(cap, recs.size() - i);
            unsigned char buf[NODE_SIZE];
            std::memset(buf, 0, NODE_SIZE);
            buf[0] = N_LEAF_ACCOUNT;
            buf[1] = static_cast<unsigned char>(ACCT_KEY);
            uint16_t const c = static_cast<uint16_t>(count);
            std::memcpy(buf + 2, &c, sizeof(c));
            unsigned char *q = buf + HDR;
            for (size_t j = 0; j < count; ++j) {
                std::memcpy(q, recs[i + j].addr.bytes, 20);
                q += 20;
                std::memcpy(q, &recs[i + j].acct, sizeof(Account));
                q += sizeof(Account);
                std::memcpy(q, &recs[i + j].sref, 8);
                q += 8;
            }
            LevelEnt e;
            std::memcpy(e.key, recs[i].addr.bytes, ACCT_KEY);
            e.ref = w.emit(buf);
            ents.push_back(e);
            i += count;
        }
        return pack_internal(w, ents, ACCT_KEY);
    }

    // ── build subcommand ────────────────────────────────────────────────
    // Write code as pages (must match trie_db.cpp): inline if it fits one page,
    // else raw data pages under an index page. Returns the code root page ref.
    uint64_t
    write_code_pages(Writer &w, unsigned char const *const code, size_t const len)
    {
        unsigned char pg[NODE_SIZE];
        std::memset(pg, 0, NODE_SIZE);
        if (len <= NODE_SIZE - CODE_INLINE_OFF) {
            pg[0] = N_CODE_INLINE;
            uint64_t const l = len;
            std::memcpy(pg + CODE_LEN, &l, 8);
            std::memcpy(pg + CODE_INLINE_OFF, code, len);
            return w.emit(pg);
        }
        size_t const np = (len + NODE_SIZE - 1) / NODE_SIZE;
        MONAD_ASSERT(np <= (NODE_SIZE - CODE_CHILDREN) / 8);
        std::vector<uint64_t> refs(np);
        for (size_t i = 0; i < np; ++i) {
            unsigned char d[NODE_SIZE];
            std::memset(d, 0, NODE_SIZE);
            size_t const n = std::min<size_t>(NODE_SIZE, len - i * NODE_SIZE);
            std::memcpy(d, code + i * NODE_SIZE, n);
            refs[i] = w.emit(d);
        }
        pg[0] = N_CODE_INDEX;
        uint64_t const l = len;
        std::memcpy(pg + CODE_LEN, &l, 8);
        uint32_t const nc = static_cast<uint32_t>(np);
        std::memcpy(pg + CODE_NCHILD, &nc, 4);
        std::memcpy(pg + CODE_CHILDREN, refs.data(), np * 8);
        return w.emit(pg);
    }

    // Bottom-up bulk-pack a B+tree in kv::blockmap format from a sorted map of
    // 32-byte key -> 8-byte value. Returns the root ref (an empty leaf if empty).
    uint64_t pack_blockmap(Writer &w, std::map<bytes32_t, uint64_t> const &m)
    {
        struct Ent
        {
            bytes32_t key;
            uint64_t ref;
        };
        std::vector<Ent> level;
        constexpr size_t KL = 32, VL = 8;
        if (m.empty()) {
            unsigned char pg[NODE_SIZE];
            std::memset(pg, 0, NODE_SIZE);
            pg[BP_TYPE] = N_BLOCKMAP_LEAF;
            pg[BP_KEYLEN] = KL;
            pg[BP_VALLEN] = VL;
            return w.emit(pg);
        }
        // leaves
        std::vector<std::pair<bytes32_t, uint64_t>> items(m.begin(), m.end());
        constexpr size_t lcap = (NODE_SIZE - BP_HDR) / (KL + VL);
        for (size_t i = 0; i < items.size(); i += lcap) {
            size_t const n = std::min(lcap, items.size() - i);
            unsigned char pg[NODE_SIZE];
            std::memset(pg, 0, NODE_SIZE);
            pg[BP_TYPE] = N_BLOCKMAP_LEAF;
            pg[BP_KEYLEN] = KL;
            pg[BP_VALLEN] = VL;
            uint16_t const c = static_cast<uint16_t>(n);
            std::memcpy(pg + BP_COUNT, &c, 2);
            unsigned char *q = pg + BP_HDR;
            for (size_t j = 0; j < n; ++j) {
                std::memcpy(q, items[i + j].first.bytes, KL);
                q += KL;
                std::memcpy(q, &items[i + j].second, VL);
                q += VL;
            }
            level.push_back({items[i].first, w.emit(pg)});
        }
        // internal levels
        constexpr size_t icap = (NODE_SIZE - BP_HDR + KL) / (8 + KL);
        while (level.size() > 1) {
            std::vector<Ent> up;
            for (size_t i = 0; i < level.size(); i += icap) {
                size_t const n = std::min(icap, level.size() - i);
                unsigned char pg[NODE_SIZE];
                std::memset(pg, 0, NODE_SIZE);
                pg[BP_TYPE] = N_BLOCKMAP_INTERNAL;
                pg[BP_KEYLEN] = KL;
                uint16_t const c = static_cast<uint16_t>(n);
                std::memcpy(pg + BP_COUNT, &c, 2);
                unsigned char *q = pg + BP_HDR;
                for (size_t j = 0; j < n; ++j) {
                    std::memcpy(q, &level[i + j].ref, 8);
                    q += 8;
                }
                for (size_t j = 1; j < n; ++j) { // separators: min key of child j
                    std::memcpy(q, level[i + j].key.bytes, KL);
                    q += KL;
                }
                up.push_back({level[i].key, w.emit(pg)});
            }
            level.swap(up);
        }
        return level[0].ref;
    }

    int do_build(
        std::filesystem::path const &root, char const *const out_path,
        bool const use_pages, uint64_t const block)
    {
        std::vector<AcctIn> accounts;
        std::vector<StorIn> storage;
        std::map<bytes32_t, byte_string> codes;
        uint64_t const shards = ingest(root, accounts, storage, codes);
        std::printf(
            "ingest: shards=%lu accounts=%zu slots=%zu format=%s\n",
            shards,
            accounts.size(),
            storage.size(),
            use_pages ? "pages" : "flat");
        MONAD_ASSERT(!accounts.empty());

        size_t const N = accounts.size();
        std::vector<uint32_t> order(N);
        for (uint32_t i = 0; i < N; ++i) {
            order[i] = i;
        }
        std::sort(order.begin(), order.end(), [&](uint32_t a, uint32_t b) {
            return std::memcmp(
                       accounts[a].addr.bytes, accounts[b].addr.bytes, 20) < 0;
        });
        std::vector<uint32_t> old2new(N);
        for (uint32_t rank = 0; rank < N; ++rank) {
            old2new[order[rank]] = rank;
        }
        for (auto &e : storage) {
            e.acct = old2new[e.acct];
        }
        std::sort(
            storage.begin(),
            storage.end(),
            [](StorIn const &a, StorIn const &b) {
                if (a.acct != b.acct) {
                    return a.acct < b.acct;
                }
                return std::memcmp(a.slot.bytes, b.slot.bytes, 32) < 0;
            });

        Writer w;
        if (is_device_target(out_path)) {
            // kvdb_base: KV owns the device tail as a flat page range, written
            // directly via our own fd (no storage_pool at runtime). Its base is
            // the physical offset of seq chunk KVDB_FIRST_SEQ_CHUNK (the triedb
            // allocation-guard boundary) — query the pool once to learn it, then
            // record it in the .kvhdr so execution needs no pool.
            {
                std::array<std::filesystem::path, 1> const srcs{
                    std::filesystem::path{out_path}};
                async::storage_pool pool{
                    std::span<std::filesystem::path const>{srcs},
                    async::storage_pool::mode::open_existing};
                w.base_offset =
                    pool.chunk(async::storage_pool::seq, KVDB_FIRST_SEQ_CHUNK)
                        .read_fd()
                        .second;
            }
            w.fd = ::open(out_path, O_RDWR);
            MONAD_ASSERT(w.fd != -1);
            std::printf(
                "device: %s base_offset=%llu (flat 4KB pages, seq chunk %u)\n",
                out_path,
                static_cast<unsigned long long>(w.base_offset),
                static_cast<unsigned>(KVDB_FIRST_SEQ_CHUNK));
        }
        else {
            w.fd = ::open(out_path, O_RDWR | O_CREAT | O_TRUNC, 0644);
            MONAD_ASSERT(w.fd != -1);
        }

        // kvdb_base multiversion: reserve the metadata region at the front of
        // KV's range so node refs start at KVDB_META_BYTES (ref 0..META_BYTES
        // holds the header + root ring). The region itself is written after the
        // root is known (write_kv_meta below).
        w.off = KVDB_META_BYTES;

        std::vector<AcctRec> recs;
        recs.reserve(N);
        uint64_t ext_nodes = 0;
        size_t si = 0;
        for (uint32_t rank = 0; rank < N; ++rank) {
            AcctIn const &a = accounts[order[rank]];
            uint64_t sref = NULL_REF;
            if (si < storage.size() && storage[si].acct == rank) {
                size_t const lo = si;
                while (si < storage.size() && storage[si].acct == rank) {
                    ++si;
                }
                sref = use_pages
                           ? pack_storage_pages(w, storage, lo, si, ext_nodes)
                           : pack_storage_flat(w, storage, lo, si);
            }
            recs.push_back({a.addr, a.acct, sref});
        }
        MONAD_ASSERT(si == storage.size());

        uint64_t const root_ref = pack_account_tree(w, recs);
        // kvdb_base multiversion: seed the block map with one leaf holding the
        // build (finalized) block: key = (block big-endian, id 0), value =
        // (block_root, parent 0, block_hash 0). id and block_hash are zero
        // (unknown from a snapshot); the base image has no KV blobs so the block
        // root is just the state root. Execution matches the finalized tip by
        // block number. Layout must match trie_db.cpp's kv::blockmap.
        uint64_t tree_root;
        {
            unsigned char buf[NODE_SIZE];
            std::memset(buf, 0, NODE_SIZE);
            buf[BP_TYPE] = N_BLOCKMAP_LEAF;
            buf[BP_KEYLEN] = static_cast<unsigned char>(BM_KL);
            buf[BP_VALLEN] = static_cast<unsigned char>(BM_VL);
            uint16_t const count = 1;
            std::memcpy(buf + BP_COUNT, &count, 2);
            unsigned char *const ent = buf + BP_HDR;
            for (int i = 0; i < 8; ++i) { // key: block big-endian, id 0
                ent[i] = static_cast<unsigned char>(block >> (56 - 8 * i));
            }
            std::memcpy(ent + BM_KL, &root_ref, 8); // value: block root
            tree_root = w.emit(buf);
        }
        // Code B+tree (key=code_hash 32B, value=code root page ref 8B): write
        // each unique code as pages, then bulk-pack the index. Execution adds
        // newly-deployed code per block.
        std::map<bytes32_t, uint64_t> code_index;
        for (auto const &[hash, bytes] : codes) {
            code_index.emplace(
                hash, write_code_pages(w, bytes.data(), bytes.size()));
        }
        uint64_t const code_tree_root = pack_blockmap(w, code_index);
        std::printf("build: code entries=%zu\n", code_index.size());
        // Empty global hash-index trees (populated at runtime by execution):
        // tx_hash(32)->(block8,idx4) and block_hash(32)->number8.
        auto empty_index = [&](size_t const kl, size_t const vl) {
            unsigned char pg[NODE_SIZE];
            std::memset(pg, 0, NODE_SIZE);
            pg[BP_TYPE] = N_BLOCKMAP_LEAF;
            pg[BP_KEYLEN] = static_cast<unsigned char>(kl);
            pg[BP_VALLEN] = static_cast<unsigned char>(vl);
            return w.emit(pg);
        };
        uint64_t const txhash_index_root = empty_index(32, 12);
        uint64_t const blockhash_index_root = empty_index(32, 8);
        uint64_t const image_bytes = w.off;
        std::printf(
            "build: nodes=%lu ext_nodes=%lu image=%.3f GiB root_ref=%lu\n",
            w.nodes,
            ext_nodes,
            static_cast<double>(image_bytes) / (1024.0 * 1024.0 * 1024.0),
            root_ref);

        // Quick in-process sanity check (full gate is the `verify` command).
        // kvdb_base: read back through a single flat mmap of the image range
        // (offset w.base_offset: phys(seq chunk 4096) for a device, 0 for a file).
        {
            unsigned char const *const base =
                static_cast<unsigned char const *>(::mmap(
                    nullptr,
                    image_bytes,
                    PROT_READ,
                    MAP_SHARED,
                    w.fd,
                    static_cast<off_t>(w.base_offset)));
            MONAD_ASSERT(base != MAP_FAILED);
            Resolver const R{base};
            size_t const astep = std::max<size_t>(1, N / 10000);
            for (size_t rank = 0; rank < N; rank += astep) {
                AcctRec const &r = recs[rank];
                unsigned char const *rec = find_account_rec(R, root_ref, r.addr);
                MONAD_ASSERT(rec != nullptr);
                MONAD_ASSERT(
                    std::memcmp(rec + 20, &r.acct, sizeof(Account)) == 0);
            }
            ::munmap(const_cast<unsigned char *>(base), image_bytes);
            std::printf("build: quick sanity ok\n");
        }

        // kvdb_base multiversion: seed the on-device metadata ring with this
        // block's root (window [block, block]). Execution advances it per block.
        write_kv_meta(
            w.fd, w.base_offset, block, tree_root, code_tree_root,
            txhash_index_root, blockhash_index_root);
        std::printf(
            "build: kv_meta seeded block=%lu ring_slot=%lu\n",
            static_cast<unsigned long>(block),
            static_cast<unsigned long>(block % KVDB_HISTORY_N));

        KvHeader hdr{};
        hdr.magic = KV_MAGIC;
        hdr.version = 6; // v6: adds front metadata region (multiversion ring)
        hdr.node_size = static_cast<uint32_t>(NODE_SIZE);
        hdr.root_ref = root_ref;
        hdr.node_count = w.nodes;
        hdr.image_bytes = image_bytes;
        hdr.num_accounts = N;
        hdr.num_slots = storage.size();
        hdr.storage_format = use_pages ? 1u : 0u;
        hdr.ext_nodes = ext_nodes;
        hdr.base_offset = w.base_offset; // device flat base (0 for a file)
        // For a device target the ".kvhdr" sidecar cannot live next to the
        // node (that would be a file under /dev); write it to the cwd basename
        // for now. Device-resident KV header is a later increment.
        std::string const super_path =
            is_device_target(out_path)
                ? std::filesystem::path{out_path}.filename().string() + ".kvhdr"
                : std::string{out_path} + ".kvhdr";
        int const sfd =
            ::open(super_path.c_str(), O_RDWR | O_CREAT | O_TRUNC, 0644);
        MONAD_ASSERT(sfd != -1);
        ssize_t const sw = ::write(sfd, &hdr, sizeof(hdr));
        MONAD_ASSERT(sw == static_cast<ssize_t>(sizeof(hdr)));
        ::close(sfd);

        if (w.fd != -1) {
            ::fsync(w.fd);
            ::close(w.fd);
        }
        // device mode: pool destructor releases fds; pwrite'd pages stay in
        // the OS cache, coherent for a same-host reader.
        std::printf("done: %s\n", out_path);
        return 0;
    }

    // ── Loader (reload path) ────────────────────────────────────────────
    struct Loader
    {
        // file mode
        Mapped img;
        // device mode: KV's own fd + a flat mmap of the image range (kvdb_base)
        int dev_fd{-1};
        // common
        KvHeader hdr{};
        Resolver R;

        void open(char const *const image_path)
        {
            bool const dev = is_device_target(image_path);
            std::string const super_path =
                dev ? std::filesystem::path{image_path}.filename().string() +
                          ".kvhdr"
                    : std::string{image_path} + ".kvhdr";
            Mapped s = map_file(super_path, /*require*/ true);
            MONAD_ASSERT(s.len == sizeof(KvHeader));
            std::memcpy(&hdr, s.data, sizeof(KvHeader));
            unmap(s);
            MONAD_ASSERT(hdr.magic == KV_MAGIC);
            MONAD_ASSERT(hdr.node_size == NODE_SIZE);
            if (dev) {
                dev_fd = ::open(image_path, O_RDONLY);
                MONAD_ASSERT(dev_fd != -1);
                R = Resolver{
                    map_kv_image_dev(dev_fd, hdr.base_offset, hdr.image_bytes)};
            }
            else {
                img = map_file(image_path, /*require*/ true);
                MONAD_ASSERT(img.len == hdr.image_bytes);
                R = Resolver{img.data};
            }
        }

        unsigned char const *read_account(Address const &addr) const
        {
            return find_account_rec(R, hdr.root_ref, addr);
        }

        static uint64_t sref_of(unsigned char const *const acct_rec)
        {
            uint64_t sref;
            std::memcpy(&sref, acct_rec + 20 + sizeof(Account), 8);
            return sref;
        }

        // Full read_storage(addr, slot): re-descends the account tree for the
        // storage-root (the prototype's (a) decision), then the subtree.
        unsigned char const *
        read_storage(Address const &addr, bytes32_t const &slot) const
        {
            unsigned char const *acct = read_account(addr);
            if (!acct) {
                return nullptr;
            }
            uint64_t const sref = sref_of(acct);
            if (sref == NULL_REF) {
                return nullptr;
            }
            return find_slot_value(R, sref, slot);
        }
    };

    // ── verify subcommand (full correctness gate) ───────────────────────
    int do_verify(
        std::filesystem::path const &root, char const *const image_path)
    {
        Loader ld;
        ld.open(image_path);
        std::printf(
            "load: root_ref=%lu nodes=%lu ext_nodes=%lu image=%.3f GiB "
            "format=%s accounts=%lu slots=%lu\n",
            ld.hdr.root_ref,
            ld.hdr.node_count,
            ld.hdr.ext_nodes,
            static_cast<double>(ld.hdr.image_bytes) /
                (1024.0 * 1024.0 * 1024.0),
            ld.hdr.storage_format ? "pages" : "flat",
            ld.hdr.num_accounts,
            ld.hdr.num_slots);

        std::vector<AcctIn> accounts;
        std::vector<StorIn> storage;
        std::map<bytes32_t, byte_string> codes_unused;
        uint64_t const shards = ingest(root, accounts, storage, codes_unused);
        std::printf(
            "ingest: shards=%lu accounts=%zu slots=%zu\n",
            shards,
            accounts.size(),
            storage.size());
        MONAD_ASSERT(accounts.size() == ld.hdr.num_accounts);
        MONAD_ASSERT(storage.size() == ld.hdr.num_slots);

        std::vector<uint64_t> sref_by_idx(accounts.size(), NULL_REF);
        size_t acct_ok = 0;
        for (size_t i = 0; i < accounts.size(); ++i) {
            unsigned char const *rec = ld.read_account(accounts[i].addr);
            MONAD_ASSERT(rec != nullptr);
            MONAD_ASSERT(
                std::memcmp(rec + 20, &accounts[i].acct, sizeof(Account)) == 0);
            sref_by_idx[i] = Loader::sref_of(rec);
            ++acct_ok;
        }
        std::printf("verify: accounts_ok=%zu (all)\n", acct_ok);

        size_t slot_ok = 0;
        for (auto const &e : storage) {
            uint64_t const sref = sref_by_idx[e.acct];
            MONAD_ASSERT(sref != NULL_REF);
            unsigned char const *v = find_slot_value(ld.R, sref, e.slot);
            MONAD_ASSERT(v != nullptr);
            MONAD_ASSERT(std::memcmp(v, e.val.bytes, 32) == 0);
            ++slot_ok;
        }
        std::printf("verify: slots_ok=%zu (all)\n", slot_ok);

        // Exercise the real read_storage(addr, slot) API on a sample.
        size_t const sstep = std::max<size_t>(1, storage.size() / 20000);
        size_t api_ok = 0;
        for (size_t k = 0; k < storage.size(); k += sstep) {
            StorIn const &e = storage[k];
            unsigned char const *v =
                ld.read_storage(accounts[e.acct].addr, e.slot);
            MONAD_ASSERT(v != nullptr);
            MONAD_ASSERT(std::memcmp(v, e.val.bytes, 32) == 0);
            ++api_ok;
        }
        std::printf("verify: read_storage_api_ok=%zu (sample)\n", api_ok);

        // Negative check: an absent slot must miss.
        {
            bytes32_t absent{};
            std::memset(absent.bytes, 0xEE, sizeof(absent.bytes));
            size_t misses = 0;
            for (size_t i = 0; i < accounts.size() && misses < 8; ++i) {
                if (sref_by_idx[i] != NULL_REF) {
                    MONAD_ASSERT(
                        find_slot_value(ld.R, sref_by_idx[i], absent) ==
                        nullptr);
                    ++misses;
                }
            }
        }

        std::printf("verify: PASS\n");
        return 0;
    }

    // ── pagestats subcommand ────────────────────────────────────────────
    int do_pagestats(std::filesystem::path const &root)
    {
        std::vector<AcctIn> accounts;
        std::vector<StorIn> storage;
        std::map<bytes32_t, byte_string> codes_unused;
        uint64_t const shards = ingest(root, accounts, storage, codes_unused);
        std::printf(
            "ingest: shards=%lu accounts=%zu slots=%zu\n",
            shards,
            accounts.size(),
            storage.size());

        std::sort(
            storage.begin(),
            storage.end(),
            [](StorIn const &a, StorIn const &b) {
                if (a.acct != b.acct) {
                    return a.acct < b.acct;
                }
                return std::memcmp(a.slot.bytes, b.slot.bytes, 32) < 0;
            });

        uint64_t pages = 0, max_pc = 0, ge127 = 0, ge120 = 0;
        uint64_t hist[9] = {0};
        size_t i = 0;
        while (i < storage.size()) {
            uint32_t const acct = storage[i].acct;
            bytes32_t const base = page_base_of(storage[i].slot);
            size_t pc = 0;
            while (i < storage.size() && storage[i].acct == acct &&
                   std::memcmp(
                       page_base_of(storage[i].slot).bytes, base.bytes, 32) ==
                       0) {
                ++pc;
                ++i;
            }
            ++pages;
            if (pc > max_pc) {
                max_pc = pc;
            }
            ge127 += (pc >= 127);
            ge120 += (pc >= 120);
            size_t const b = pc <= 1     ? 0
                             : pc <= 2   ? 1
                             : pc <= 4   ? 2
                             : pc <= 8   ? 3
                             : pc <= 16  ? 4
                             : pc <= 32  ? 5
                             : pc <= 64  ? 6
                             : pc <= 126 ? 7
                                         : 8;
            ++hist[b];
        }

        std::printf(
            "pages=%lu max_popcount=%lu avg_slots/page=%.2f\n",
            pages,
            max_pc,
            static_cast<double>(storage.size()) /
                static_cast<double>(pages ? pages : 1));
        char const *labels[9] = {
            "==1", "==2", "3-4", "5-8", "9-16", "17-32", "33-64", "65-126",
            ">=127"};
        for (size_t k = 0; k < 9; ++k) {
            std::printf(
                "  popcount %-7s : %10lu pages (%.2f%%)\n",
                labels[k],
                hist[k],
                100.0 * static_cast<double>(hist[k]) /
                    static_cast<double>(pages ? pages : 1));
        }
        std::printf(
            "pages needing extension (>=127) = %lu ; >=120 = %lu\n",
            ge127,
            ge120);
        return 0;
    }
}

int main(int argc, char **argv)
{
    if (argc >= 5 && std::strcmp(argv[1], "build") == 0) {
        std::filesystem::path const root =
            std::filesystem::path{argv[2]} / argv[3];
        MONAD_ASSERT(std::filesystem::is_directory(root));
        bool use_pages = true; // default
        if (argc >= 6) {
            if (std::strcmp(argv[5], "flat") == 0) {
                use_pages = false;
            }
            else if (std::strcmp(argv[5], "pages") == 0) {
                use_pages = true;
            }
            else {
                std::fprintf(stderr, "unknown format '%s'\n", argv[5]);
                return 2;
            }
        }
        uint64_t const block = std::strtoull(argv[3], nullptr, 10);
        return do_build(root, argv[4], use_pages, block);
    }
    if (argc >= 4 && std::strcmp(argv[1], "pagestats") == 0) {
        std::filesystem::path const root =
            std::filesystem::path{argv[2]} / argv[3];
        MONAD_ASSERT(std::filesystem::is_directory(root));
        return do_pagestats(root);
    }
    if (argc >= 5 && std::strcmp(argv[1], "verify") == 0) {
        std::filesystem::path const root =
            std::filesystem::path{argv[2]} / argv[3];
        MONAD_ASSERT(std::filesystem::is_directory(root));
        return do_verify(root, argv[4]);
    }
    std::fprintf(
        stderr,
        "usage:\n"
        "  %s build     <snapshot_dir> <block> <out_image> [flat|pages]\n"
        "  %s verify    <snapshot_dir> <block> <image>\n"
        "  %s pagestats <snapshot_dir> <block>\n",
        argv[0],
        argv[0],
        argv[0]);
    return 2;
}
