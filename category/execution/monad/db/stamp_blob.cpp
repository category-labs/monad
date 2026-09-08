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

#include <category/core/assert.h>
#include <category/core/byte_string.hpp>
#include <category/core/keccak.hpp>
#include <category/execution/ethereum/db/storage_key.hpp>
#include <category/execution/monad/db/stamp_blob.hpp>

#include <algorithm>
#include <charconv>
#include <cstring>
#include <fstream>

MONAD_NAMESPACE_BEGIN

namespace
{
    constexpr char MAGIC[8] = {'M', 'B', 'S', 'T', 'A', 'M', 'P', '1'};
    constexpr size_t ACCOUNT_RECORD_SIZE = 20 + 8 + 1 + 1;
    constexpr size_t STORAGE_RECORD_SIZE = StorageKey::k_bytes + 8 + 4 + 4;

    void put_u64(byte_string &out, uint64_t const v)
    {
        for (unsigned i = 0; i < 8; ++i) {
            out.push_back(static_cast<unsigned char>(v >> (8 * i)));
        }
    }

    void put_u32(byte_string &out, uint32_t const v)
    {
        for (unsigned i = 0; i < 4; ++i) {
            out.push_back(static_cast<unsigned char>(v >> (8 * i)));
        }
    }

    uint64_t get_u64(unsigned char const *const p)
    {
        uint64_t v = 0;
        for (unsigned i = 0; i < 8; ++i) {
            v |= static_cast<uint64_t>(p[i]) << (8 * i);
        }
        return v;
    }

    uint32_t get_u32(unsigned char const *const p)
    {
        uint32_t v = 0;
        for (unsigned i = 0; i < 4; ++i) {
            v |= static_cast<uint32_t>(p[i]) << (8 * i);
        }
        return v;
    }
}

void write_stamp_blob(
    std::filesystem::path const &dir, uint64_t const block,
    std::vector<AccountStampRecord> const &accounts,
    std::vector<StorageStampRecord> const &storage)
{
    byte_string payload;
    payload.reserve(
        sizeof(MAGIC) + 16 + accounts.size() * ACCOUNT_RECORD_SIZE +
        storage.size() * STORAGE_RECORD_SIZE);
    payload.append(
        reinterpret_cast<unsigned char const *>(MAGIC), sizeof(MAGIC));
    put_u64(payload, block);
    put_u32(payload, static_cast<uint32_t>(accounts.size()));
    put_u32(payload, static_cast<uint32_t>(storage.size()));
    for (auto const &r : accounts) {
        payload.append(r.address.bytes, sizeof(r.address.bytes));
        put_u64(payload, r.prev_stamp);
        payload.push_back(r.prev_weight);
        payload.push_back(r.weight);
    }
    for (auto const &r : storage) {
        payload.append(r.key.bytes, sizeof(r.key.bytes));
        put_u64(payload, r.prev_stamp);
        put_u32(payload, r.prev_weight);
        put_u32(payload, r.weight);
    }
    auto const hash = keccak256({payload.data(), payload.size()});

    std::filesystem::create_directories(dir);
    std::ofstream out(
        dir / (std::to_string(block) + ".blob"),
        std::ios::binary | std::ios::trunc);
    MONAD_ASSERT(out.good());
    out.write(
        reinterpret_cast<char const *>(payload.data()),
        static_cast<std::streamsize>(payload.size()));
    out.write(reinterpret_cast<char const *>(hash.bytes), sizeof(hash.bytes));
    MONAD_ASSERT(out.good());
}

std::optional<StampBlob> read_stamp_blob(std::filesystem::path const &file)
{
    std::ifstream in(file, std::ios::binary | std::ios::ate);
    if (!in.good()) {
        return std::nullopt;
    }
    auto const total = static_cast<size_t>(in.tellg());
    if (total < sizeof(MAGIC) + 16 + 32) {
        return std::nullopt;
    }
    std::vector<unsigned char> buf(total);
    in.seekg(0);
    in.read(
        reinterpret_cast<char *>(buf.data()),
        static_cast<std::streamsize>(total));
    if (!in.good()) {
        return std::nullopt;
    }
    size_t const payload_size = total - 32;
    auto const hash = keccak256({buf.data(), payload_size});
    if (std::memcmp(hash.bytes, buf.data() + payload_size, 32) != 0) {
        return std::nullopt;
    }
    unsigned char const *p = buf.data();
    if (std::memcmp(p, MAGIC, sizeof(MAGIC)) != 0) {
        return std::nullopt;
    }
    p += sizeof(MAGIC);
    StampBlob blob;
    blob.block = get_u64(p);
    p += 8;
    uint32_t const n_accounts = get_u32(p);
    p += 4;
    uint32_t const n_storage = get_u32(p);
    p += 4;
    if (payload_size != sizeof(MAGIC) + 16 + n_accounts * ACCOUNT_RECORD_SIZE +
                            n_storage * STORAGE_RECORD_SIZE) {
        return std::nullopt;
    }
    blob.account_stamps.reserve(n_accounts);
    for (uint32_t i = 0; i < n_accounts; ++i) {
        AccountStampRecord r;
        std::memcpy(r.address.bytes, p, sizeof(r.address.bytes));
        p += sizeof(r.address.bytes);
        r.prev_stamp = get_u64(p);
        p += 8;
        r.prev_weight = *p++;
        r.weight = *p++;
        blob.account_stamps.push_back(r);
    }
    blob.storage_stamps.reserve(n_storage);
    for (uint32_t i = 0; i < n_storage; ++i) {
        StorageStampRecord r;
        std::memcpy(r.key.bytes, p, sizeof(r.key.bytes));
        p += sizeof(r.key.bytes);
        r.prev_stamp = get_u64(p);
        p += 8;
        r.prev_weight = get_u32(p);
        p += 4;
        r.weight = get_u32(p);
        p += 4;
        blob.storage_stamps.push_back(r);
    }
    return blob;
}

std::vector<uint64_t> list_stamp_blobs(std::filesystem::path const &dir)
{
    std::vector<uint64_t> blocks;
    std::error_code ec;
    for (auto const &entry : std::filesystem::directory_iterator(dir, ec)) {
        if (!entry.is_regular_file() || entry.path().extension() != ".blob") {
            continue;
        }
        auto const stem = entry.path().stem().string();
        uint64_t block = 0;
        auto const [end, err] =
            std::from_chars(stem.data(), stem.data() + stem.size(), block);
        if (err == std::errc{} && end == stem.data() + stem.size()) {
            blocks.push_back(block);
        }
    }
    std::sort(blocks.begin(), blocks.end());
    return blocks;
}

MONAD_NAMESPACE_END
