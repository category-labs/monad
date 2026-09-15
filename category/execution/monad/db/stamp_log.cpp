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

#include <category/execution/monad/db/stamp_log.hpp>

#include <category/core/assert.h>

#include <array>
#include <cstring>
#include <limits>

MONAD_NAMESPACE_BEGIN

namespace
{
    constexpr uint64_t MAGIC = 0x32474e495243424dULL;

    void put(std::span<uint8_t> out, size_t offset, uint64_t value)
    {
        for (size_t i = 0; i < 8; ++i) {
            out[offset + i] = static_cast<uint8_t>(value >> (8 * i));
        }
    }

    uint64_t get(std::span<uint8_t const> in, size_t offset)
    {
        uint64_t value = 0;
        for (size_t i = 0; i < 8; ++i) {
            value |= uint64_t{in[offset + i]} << (8 * i);
        }
        return value;
    }

    storage_page_t page_of(std::span<uint8_t const> bytes)
    {
        storage_page_t page;
        MONAD_ASSERT(bytes.size() <= STAMP_LOG_PAGE_BYTES);
        for (size_t i = 0; i < bytes.size(); i += 32) {
            bytes32_t word{};
            std::memcpy(
                word.bytes,
                bytes.data() + i,
                std::min(size_t{32}, bytes.size() - i));
            page.set(static_cast<uint8_t>(i / 32), word);
        }
        return page;
    }

    std::array<uint8_t, STAMP_LOG_PAGE_BYTES>
    bytes_of(storage_page_t const &page)
    {
        std::array<uint8_t, STAMP_LOG_PAGE_BYTES> out{};
        for (size_t i = 0; i < 128; ++i) {
            auto const word = page[static_cast<uint8_t>(i)];
            std::memcpy(out.data() + i * 32, word.bytes, 32);
        }
        return out;
    }

    uint64_t generation(CacheRingConfig const &config, uint64_t stamp)
    {
        MONAD_ASSERT(stamp > 0);
        return (stamp - 1) / config.records_per_index + 1;
    }

    uint64_t first_record(CacheRingConfig const &config, uint64_t gen)
    {
        MONAD_ASSERT(
            gen > 0 && gen <= (std::numeric_limits<int64_t>::max() - 1) /
                                  config.records_per_index);
        return (gen - 1) * config.records_per_index + 1;
    }
}

bytes32_t
cache_ring_key(CacheRingConfig const &config, CacheRingPart part, uint64_t gen)
{
    bytes32_t key{};
    // Page keys have 249 bits: state sync expands them to 256-bit slot
    // keys by shifting left seven. Keep the namespace within that range.
    key.bytes[0] = 0x01;
    // A distinct namespace prevents reading the old per-ring cursor format.
    key.bytes[1] = part == CacheRingPart::cursor
                       ? 2
                       : static_cast<uint8_t>(config.kind);
    key.bytes[2] = static_cast<uint8_t>(part);
    uint64_t index = 0;
    if (part != CacheRingPart::cursor) {
        MONAD_ASSERT(gen > 0);
        index = gen % config.indices;
    }
    for (size_t i = 0; i < 8; ++i) {
        key.bytes[31 - i] = static_cast<uint8_t>(index >> (8 * i));
    }
    return key;
}

storage_page_t encode_cache_cursor(
    CacheRingConfig const &config, CacheRingCursor const &cursor)
{
    std::array<uint8_t, 96> out{};
    uint64_t const fields[] = {
        MAGIC,
        static_cast<uint64_t>(config.kind),
        config.records_per_index,
        config.indices,
        config.capacity,
        config.renewal,
        cursor.view.floor,
        cursor.view.next,
        cursor.view.refresh,
        cursor.total_charge,
        cursor.floor_charge,
        0};
    for (size_t i = 0; i < std::size(fields); ++i) {
        put(out, i * 8, fields[i]);
    }
    return page_of(out);
}

CacheRingCursor
decode_cache_cursor(CacheRingConfig const &config, storage_page_t const &page)
{
    auto const bytes = bytes_of(page);
    MONAD_ASSERT(
        get(bytes, 0) == MAGIC &&
        get(bytes, 8) == static_cast<uint64_t>(config.kind));
    MONAD_ASSERT(
        get(bytes, 16) == config.records_per_index &&
        get(bytes, 24) == config.indices);
    MONAD_ASSERT(
        get(bytes, 32) == config.capacity && get(bytes, 40) == config.renewal);
    CacheRingCursor out{
        {get(bytes, 48), get(bytes, 56), get(bytes, 64)},
        get(bytes, 72),
        get(bytes, 80)};
    MONAD_ASSERT(out.view.floor >= 1 && out.view.next >= out.view.floor);
    MONAD_ASSERT(
        out.view.next <=
        static_cast<uint64_t>(std::numeric_limits<int64_t>::max()));
    MONAD_ASSERT((out.view.floor - 1) % config.records_per_index == 0);
    MONAD_ASSERT(
        out.view.refresh >= out.view.floor &&
        (out.view.refresh - 1) % config.records_per_index == 0);
    MONAD_ASSERT(
        out.view.refresh <=
        first_record(config, generation(config, out.view.next) + 1));
    MONAD_ASSERT(
        out.total_charge >= out.floor_charge &&
        out.total_charge - out.floor_charge <= config.capacity);
    MONAD_ASSERT(encode_cache_cursor(config, out) == page);
    return out;
}

storage_page_t
encode_cache_chunk(CacheRingConfig const &config, CacheRingChunk const &chunk)
{
    MONAD_ASSERT(
        chunk.generation > 0 &&
        chunk.records.size() <= config.records_per_index);
    std::array<uint8_t, STAMP_LOG_PAGE_BYTES> bytes{};
    put(bytes, 0, MAGIC);
    put(bytes, 8, static_cast<uint64_t>(config.kind));
    put(bytes, 16, chunk.generation);
    put(bytes, 24, chunk.begin_charge);
    put(bytes, 32, chunk.charge);
    put(bytes, 40, chunk.records.size());
    size_t offset = CACHE_RING_HEADER_BYTES;
    uint64_t charge = 0;
    for (auto const &record : chunk.records) {
        size_t const key_size =
            config.kind == CacheRingKind::accounts ? 20 : 60;
        MONAD_ASSERT(
            offset + key_size + (key_size == 60 ? size_t{2} : size_t{1}) <=
            bytes.size());
        std::memcpy(bytes.data() + offset, record.key.bytes, key_size);
        offset += key_size;
        MONAD_ASSERT(record.weight >= 1 && record.weight <= 128);
        if (key_size == 20) {
            MONAD_ASSERT(record.weight == 1);
        }
        if (key_size == 60)
            bytes[offset++] = record.weight;
        bytes[offset++] = record.deleted ? 1 : 0;
        charge += record.weight;
    }
    MONAD_ASSERT(charge == chunk.charge);
    return page_of(bytes);
}

CacheRingChunk decode_cache_chunk(
    CacheRingConfig const &config, storage_page_t const &page, uint64_t gen)
{
    auto const bytes = bytes_of(page);
    MONAD_ASSERT(
        get(bytes, 0) == MAGIC &&
        get(bytes, 8) == static_cast<uint64_t>(config.kind));
    MONAD_ASSERT(get(bytes, 16) == gen);
    CacheRingChunk out{gen, get(bytes, 24), get(bytes, 32), {}};
    uint64_t const count = get(bytes, 40);
    MONAD_ASSERT(count > 0 && count <= config.records_per_index);
    size_t offset = CACHE_RING_HEADER_BYTES;
    for (uint64_t i = 0; i < count; ++i) {
        CacheRingRecord record{};
        size_t const key_size =
            config.kind == CacheRingKind::accounts ? 20 : 60;
        std::memcpy(record.key.bytes, bytes.data() + offset, key_size);
        offset += key_size;
        if (key_size == 60) {
            record.weight = bytes[offset++];
        }
        else {
            MONAD_ASSERT(record.weight == 1);
        }
        MONAD_ASSERT(bytes[offset] <= 1);
        record.deleted = bytes[offset++] != 0;
        out.records.push_back(record);
    }
    for (size_t i = offset; i < bytes.size(); ++i)
        MONAD_ASSERT(bytes[i] == 0);
    MONAD_ASSERT(encode_cache_chunk(config, out) == page);
    return out;
}

CacheRingCursor
read_cache_cursor(CacheRingConfig const &config, CachePageReader const &reader)
{
    auto const page = reader(cache_ring_key(config, CacheRingPart::cursor));
    if (!page) {
        return {};
    }
    storage_page_t region;
    uint8_t const offset = config.kind == CacheRingKind::accounts ? 0 : 3;
    for (uint8_t i = 0; i < 3; ++i) {
        region.set(i, (*page)[static_cast<uint8_t>(offset + i)]);
    }
    return region.is_empty() ? CacheRingCursor{}
                             : decode_cache_cursor(config, region);
}

CacheRingWriter::CacheRingWriter(CacheRingConfig config, CachePageReader reader)
    : config_{config}
    , reader_{std::move(reader)}
    , cursor_{read_cache_cursor(config_, reader_)}
{
    MONAD_ASSERT(
        config.records_per_index > 0 && config.records_per_index <= 192);
    MONAD_ASSERT(
        config.indices > 2 &&
        uint64_t{config.indices - 2} * config.records_per_index >=
            config.capacity);
    MONAD_ASSERT(config.renewal > 0 && config.renewal <= config.capacity);
}

CacheRingChunk &CacheRingWriter::chunk(uint64_t gen)
{
    auto it = chunks_.find(gen);
    if (it != chunks_.end()) {
        return it->second;
    }
    auto page = reader_(cache_ring_key(config_, CacheRingPart::records, gen));
    MONAD_ASSERT_PRINTF(page.has_value(), "missing cache ring chunk %lu", gen);
    return chunks_.emplace(gen, decode_cache_chunk(config_, *page, gen))
        .first->second;
}

void CacheRingWriter::advance_boundaries()
{
    auto &view = cursor_.view;
    while (cursor_.total_charge - cursor_.floor_charge > config_.capacity) {
        auto const gen = generation(config_, view.floor);
        auto const &old = chunk(gen);
        MONAD_ASSERT(old.records.size() == config_.records_per_index);
        cursor_.floor_charge = old.begin_charge + old.charge;
        view.floor = first_record(config_, gen + 1);
    }
    view.refresh = std::max(view.refresh, view.floor);
    while (view.refresh < view.next) {
        auto const gen = generation(config_, view.refresh);
        if (cursor_.total_charge - chunk(gen).begin_charge < config_.renewal) {
            break;
        }
        view.refresh = first_record(config_, gen + 1);
    }
}

uint64_t CacheRingWriter::append(CacheRingRecord const &record)
{
    auto &view = cursor_.view;
    uint64_t const stamp = view.next;
    uint64_t const gen = generation(config_, stamp);
    size_t const offset = (stamp - 1) % config_.records_per_index;
    if (offset == 0) {
        MONAD_ASSERT(
            gen < config_.indices ||
            gen - config_.indices < generation(config_, view.floor));
        chunks_[gen] = CacheRingChunk{gen, cursor_.total_charge, 0, {}};
    }
    auto &current = chunk(gen);
    MONAD_ASSERT(current.records.size() == offset);
    MONAD_ASSERT(record.weight > 0 && record.weight <= 128);
    MONAD_ASSERT(config_.kind != CacheRingKind::accounts || record.weight == 1);
    MONAD_ASSERT(
        cursor_.total_charge <=
        std::numeric_limits<uint64_t>::max() - record.weight);
    MONAD_ASSERT(
        view.next < static_cast<uint64_t>(std::numeric_limits<int64_t>::max()));
    current.records.push_back(record);
    current.charge += record.weight;
    cursor_.total_charge += record.weight;
    ++view.next;
    MONAD_ASSERT(current.charge <= config_.capacity);
    advance_boundaries();
    // Encode each modified chunk only once, in finish().
    updates_.try_emplace(cache_ring_key(config_, CacheRingPart::records, gen));
    changed_ = true;
    cursor_changed_ = true;
    return stamp;
}

bool CacheRingWriter::erase(uint64_t stamp)
{
    if (!cache_stamp_cached(stamp, cursor_.view)) {
        return false;
    }
    uint64_t const gen = generation(config_, stamp);
    size_t const offset = (stamp - 1) % config_.records_per_index;
    auto &old = chunk(gen).records.at(offset);
    if (old.deleted) {
        return false;
    }
    old.deleted = true;
    updates_.try_emplace(cache_ring_key(config_, CacheRingPart::records, gen));
    changed_ = true;
    return true;
}

CachePageUpdates CacheRingWriter::finish()
{
    CachePageUpdates out;
    finish(out);
    return out;
}

void CacheRingWriter::finish(CachePageUpdates &out)
{
    if (!changed_) {
        return;
    }
    for (auto const &[gen, value] : chunks_) {
        auto it =
            updates_.find(cache_ring_key(config_, CacheRingPart::records, gen));
        if (it != updates_.end()) {
            it->second = encode_cache_chunk(config_, value);
        }
    }
    if (cursor_changed_) {
        auto const key = cache_ring_key(config_, CacheRingPart::cursor);
        auto [it, inserted] = out.try_emplace(key);
        if (inserted) {
            it->second = reader_(key).value_or(storage_page_t{});
        }
        auto const region = encode_cache_cursor(config_, cursor_);
        uint8_t const offset = config_.kind == CacheRingKind::accounts ? 0 : 3;
        for (uint8_t i = 0; i < 3; ++i) {
            it->second.set(static_cast<uint8_t>(offset + i), region[i]);
        }
    }
    out.merge(updates_);
}

void visit_cache_ring(
    CacheRingConfig const &config, CachePageReader const &reader,
    std::function<void(CacheRingRecord const &, uint64_t, bool)> const &visit)
{
    auto const cursor = read_cache_cursor(config, reader);
    auto const &view = cursor.view;
    uint64_t charge = cursor.floor_charge;
    for (uint64_t first = view.floor; first < view.next;
         first += config.records_per_index) {
        auto const gen = generation(config, first);
        auto page = reader(cache_ring_key(config, CacheRingPart::records, gen));
        MONAD_ASSERT(page.has_value());
        auto const chunk = decode_cache_chunk(config, *page, gen);
        MONAD_ASSERT(chunk.begin_charge == charge);
        size_t const count = static_cast<size_t>(
            std::min(uint64_t{config.records_per_index}, view.next - first));
        MONAD_ASSERT(chunk.records.size() == count);
        for (size_t i = 0; i < count; ++i) {
            visit(chunk.records[i], first + i, chunk.records[i].deleted);
        }
        charge += chunk.charge;
    }
    MONAD_ASSERT(charge == cursor.total_charge);
}

uint64_t resolve_cache_stamp(
    CacheRingConfig const &config, CachePageReader const &reader,
    StorageKey const &key)
{
    uint64_t stamp = 0;
    size_t const bytes = config.kind == CacheRingKind::accounts ? 20 : 60;
    visit_cache_ring(
        config,
        reader,
        [&](CacheRingRecord const &record, uint64_t sequence, bool deleted) {
            if (std::memcmp(record.key.bytes, key.bytes, bytes) == 0) {
                stamp = deleted ? 0 : sequence;
            }
        });
    return stamp;
}

MONAD_NAMESPACE_END
