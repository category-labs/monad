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

#include <category/mpt/node.hpp>

#include <category/core/assert.h>
#include <category/core/byte_string.hpp>
#include <category/core/runtime/unaligned.hpp>
#include <category/mpt/compute.hpp>
#include <category/mpt/config.hpp>
#include <category/mpt/nibbles_view.hpp>
#include <category/mpt/util.hpp>

#include <algorithm>
#include <bit>
#include <cassert>
#include <cstddef>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <limits>
#include <optional>
#include <span>
#include <utility>
#include <vector>

MONAD_MPT_NAMESPACE_BEGIN

Node::Node(prevent_public_construction_tag) {}

Node::Node(
    prevent_public_construction_tag, uint16_t const mask,
    std::optional<byte_string_view> const value, size_t const data_size,
    NibblesView const path, int64_t const version)
    : mask(mask)
    , path_nibble_index_end(path.end_nibble_)
    , value_len(static_cast<decltype(value_len)>(
          value.transform(&byte_string_view::size).value_or(0)))
    , version(version)
{
    MONAD_ASSERT(!value || value->size() == value_len);
    bitpacked.path_nibble_index_start = path.begin_nibble_;
    bitpacked.has_value = value.has_value();

    MONAD_ASSERT(data_size <= Node::max_data_len);
    bitpacked.data_len = static_cast<uint8_t>(data_size & Node::max_data_len);

    std::ranges::copy(path.data_span(), path_data());

    if (value_len) {
        std::ranges::copy(*value, value_data());
    }
}

Node::~Node()
{
    for (Node::SharedPtr &sp : child_next_data()) {
        sp.~SharedPtr();
    }
}

unsigned Node::to_child_index(unsigned const branch) const noexcept
{
    // convert the enabled i'th bit in a 16-bit mask into its corresponding
    // index location - index
    return bitmask_index(mask, branch);
}

unsigned Node::number_of_children() const noexcept
{
    return static_cast<unsigned>(std::popcount(mask));
}

std::span<unaligned_t<chunk_offset_t>> Node::child_fnext_data() noexcept
{
    return as_unaligned_span<chunk_offset_t>(fnext_data, number_of_children());
}

std::span<unaligned_t<chunk_offset_t> const>
Node::child_fnext_data() const noexcept
{
    return as_unaligned_span<chunk_offset_t>(fnext_data, number_of_children());
}

chunk_offset_t const Node::fnext(unsigned const index) const noexcept
{
    MONAD_ASSERT(index < number_of_children());
    return child_fnext_data()[index];
}

void Node::set_fnext(unsigned const index, chunk_offset_t const off) noexcept
{
    child_fnext_data()[index] = off;
}

std::span<unaligned_t<compact_virtual_chunk_offset_t>>
Node::child_min_offset_fast_data() noexcept
{
    unsigned const n = number_of_children();
    return as_unaligned_span<compact_virtual_chunk_offset_t>(
        fnext_data + n * sizeof(chunk_offset_t), n);
}

std::span<unaligned_t<compact_virtual_chunk_offset_t> const>
Node::child_min_offset_fast_data() const noexcept
{
    unsigned const n = number_of_children();
    return as_unaligned_span<compact_virtual_chunk_offset_t>(
        fnext_data + n * sizeof(chunk_offset_t), n);
}

compact_virtual_chunk_offset_t
Node::min_offset_fast(unsigned const index) const noexcept
{
    return child_min_offset_fast_data()[index];
}

void Node::set_min_offset_fast(
    unsigned const index, compact_virtual_chunk_offset_t const offset) noexcept
{
    child_min_offset_fast_data()[index] = offset;
}

std::span<unaligned_t<compact_virtual_chunk_offset_t>>
Node::child_min_offset_slow_data() noexcept
{
    unsigned const n = number_of_children();
    auto const fast = child_min_offset_fast_data();
    return as_unaligned_span<compact_virtual_chunk_offset_t>(
        reinterpret_cast<unsigned char *>(fast.data()) + fast.size_bytes(), n);
}

std::span<unaligned_t<compact_virtual_chunk_offset_t> const>
Node::child_min_offset_slow_data() const noexcept
{
    unsigned const n = number_of_children();
    auto const fast = child_min_offset_fast_data();
    return as_unaligned_span<compact_virtual_chunk_offset_t>(
        reinterpret_cast<unsigned char const *>(fast.data()) +
            fast.size_bytes(),
        n);
}

compact_virtual_chunk_offset_t
Node::min_offset_slow(unsigned const index) const noexcept
{
    return child_min_offset_slow_data()[index];
}

void Node::set_min_offset_slow(
    unsigned const index, compact_virtual_chunk_offset_t const offset) noexcept
{
    child_min_offset_slow_data()[index] = offset;
}

compact_offset_pair Node::min_offsets(unsigned const index) const noexcept
{
    return {min_offset_fast(index), min_offset_slow(index)};
}

void Node::set_min_offsets(
    unsigned const index, compact_offset_pair const offsets) noexcept
{
    set_min_offset_fast(index, offsets.fast);
    set_min_offset_slow(index, offsets.slow);
}

std::span<unaligned_t<int64_t>> Node::child_min_version_data() noexcept
{
    unsigned const n = number_of_children();
    auto const slow = child_min_offset_slow_data();
    return as_unaligned_span<int64_t>(
        reinterpret_cast<unsigned char *>(slow.data()) + slow.size_bytes(), n);
}

std::span<unaligned_t<int64_t> const>
Node::child_min_version_data() const noexcept
{
    unsigned const n = number_of_children();
    auto const slow = child_min_offset_slow_data();
    return as_unaligned_span<int64_t>(
        reinterpret_cast<unsigned char const *>(slow.data()) +
            slow.size_bytes(),
        n);
}

int64_t Node::subtrie_min_version(unsigned const index) const noexcept
{
    return child_min_version_data()[index];
}

void Node::set_subtrie_min_version(
    unsigned const index, int64_t const min_version) noexcept
{
    child_min_version_data()[index] = min_version;
}

std::span<unaligned_t<uint16_t>> Node::child_off_data() noexcept
{
    unsigned const n = number_of_children();
    auto const versions = child_min_version_data();
    return as_unaligned_span<uint16_t>(
        reinterpret_cast<unsigned char *>(versions.data()) +
            versions.size_bytes(),
        n);
}

std::span<unaligned_t<uint16_t> const> Node::child_off_data() const noexcept
{
    unsigned const n = number_of_children();
    auto const versions = child_min_version_data();
    return as_unaligned_span<uint16_t>(
        reinterpret_cast<unsigned char const *>(versions.data()) +
            versions.size_bytes(),
        n);
}

uint16_t Node::child_data_offset(unsigned const index) const noexcept
{
    MONAD_ASSERT(index <= number_of_children());
    if (index == 0) {
        return 0;
    }
    return child_off_data()[index - 1];
}

unsigned Node::child_data_len(unsigned const index) const
{
    return child_data_offset(index + 1) - child_data_offset(index);
}

unsigned Node::child_data_len()
{
    return child_data_offset(number_of_children()) - child_data_offset(0);
}

unsigned char *Node::path_data() noexcept
{
    auto const off = child_off_data();
    return reinterpret_cast<unsigned char *>(off.data()) + off.size_bytes();
}

unsigned char const *Node::path_data() const noexcept
{
    auto const off = child_off_data();
    return reinterpret_cast<unsigned char const *>(off.data()) +
           off.size_bytes();
}

unsigned Node::path_nibbles_len() const noexcept
{
    MONAD_ASSERT(bitpacked.path_nibble_index_start <= path_nibble_index_end);
    return path_nibble_index_end - bitpacked.path_nibble_index_start;
}

bool Node::has_path() const noexcept
{
    return path_nibbles_len() > 0;
}

unsigned Node::path_bytes() const noexcept
{
    return (path_nibble_index_end + 1) / 2;
}

NibblesView Node::path_nibble_view() const noexcept
{
    return NibblesView{
        bitpacked.path_nibble_index_start, path_nibble_index_end, path_data()};
}

unsigned Node::path_start_nibble() const noexcept
{
    return bitpacked.path_nibble_index_start;
}

unsigned char *Node::value_data() noexcept
{
    return path_data() + path_bytes();
}

unsigned char const *Node::value_data() const noexcept
{
    return path_data() + path_bytes();
}

bool Node::has_value() const noexcept
{
    return bitpacked.has_value;
}

byte_string_view Node::value() const noexcept
{
    MONAD_ASSERT(has_value());
    return {value_data(), value_len};
}

std::optional<byte_string_view> Node::opt_value() const noexcept
{
    if (has_value()) {
        return value();
    }
    return std::nullopt;
}

unsigned char *Node::data_data() noexcept
{
    return value_data() + value_len;
}

unsigned char const *Node::data_data() const noexcept
{
    return value_data() + value_len;
}

byte_string_view Node::data() const noexcept
{
    return {data_data(), bitpacked.data_len};
}

unsigned char *Node::child_data() noexcept
{
    return data_data() + bitpacked.data_len;
}

unsigned char const *Node::child_data() const noexcept
{
    return data_data() + bitpacked.data_len;
}

byte_string_view Node::child_data_view(unsigned const index) const noexcept
{
    MONAD_ASSERT(index < number_of_children());
    return byte_string_view{
        child_data() + child_data_offset(index),
        static_cast<size_t>(child_data_len(index))};
}

unsigned char *Node::child_data(unsigned const index) noexcept
{
    MONAD_ASSERT(index < number_of_children());
    return child_data() + child_data_offset(index);
}

unsigned char const *Node::child_data(unsigned const index) const noexcept
{
    MONAD_ASSERT(index < number_of_children());
    return child_data() + child_data_offset(index);
}

void Node::set_child_data(
    unsigned const index, byte_string_view const data) noexcept
{
    // called after data_off array is calculated
    std::memcpy(child_data(index), data.data(), data.size());
}

unsigned char *Node::next_data() noexcept
{
    return child_data() + child_data_offset(number_of_children());
}

unsigned char const *Node::next_data() const noexcept
{
    return child_data() + child_data_offset(number_of_children());
}

// round up to 8-byte boundary
unsigned char *Node::next_data_aligned() noexcept
{
    return reinterpret_cast<unsigned char *>(
        round_up_align<3>(reinterpret_cast<uintptr_t>(next_data())));
}

unsigned char const *Node::next_data_aligned() const noexcept
{
    return reinterpret_cast<unsigned char *>(
        round_up_align<3>(reinterpret_cast<uintptr_t>(next_data())));
}

uint32_t Node::get_disk_size() const noexcept
{
    auto const *const nd = next_data();
    MONAD_ASSERT(nd >= (unsigned char *)this);
    auto const node_disk_size =
        static_cast<uint32_t>(nd - (unsigned char *)this);
    uint32_t const total_disk_size = node_disk_size + Node::disk_size_bytes;
    MONAD_ASSERT(total_disk_size <= Node::max_disk_size);
    return total_disk_size;
}

std::span<Node::SharedPtr> Node::child_next_data() noexcept
{
    return {
        reinterpret_cast<SharedPtr *>(next_data_aligned()),
        number_of_children()};
}

std::span<Node::SharedPtr const> Node::child_next_data() const noexcept
{
    return {
        reinterpret_cast<SharedPtr const *>(next_data_aligned()),
        number_of_children()};
}

Node::SharedPtr *Node::child_ptr(unsigned const index) noexcept
{
    return child_next_data().data() + index;
}

Node::SharedPtr const *Node::child_ptr(unsigned const index) const noexcept
{
    return child_next_data().data() + index;
}

Node::SharedPtr &Node::next(unsigned const index) noexcept
{
    return child_next_data()[index];
}

Node::SharedPtr const &Node::next(unsigned const index) const noexcept
{
    return child_next_data()[index];
}

void Node::set_next(unsigned const index, Node::SharedPtr p) noexcept
{
    child_next_data()[index] = std::move(p);
}

Node::SharedPtr Node::move_next(unsigned const index) noexcept
{
    return std::exchange(child_next_data()[index], SharedPtr{});
}

unsigned Node::get_mem_size() const noexcept
{
    auto const ptrs = child_next_data();
    auto const mem_size = static_cast<unsigned>(
        reinterpret_cast<unsigned char const *>(ptrs.data() + ptrs.size()) -
        reinterpret_cast<unsigned char const *>(this));
    MONAD_ASSERT(mem_size <= Node::max_size);
    return mem_size;
}

bool ChildData::is_valid() const
{
    return branch != INVALID_BRANCH;
}

void ChildData::erase()
{
    MONAD_ASSERT(!ptr);
    branch = INVALID_BRANCH;
}

void ChildData::finalize(
    Node::SharedPtr node, Compute &compute, bool const cache)
{
    MONAD_ASSERT(is_valid());
    ptr = std::move(node);
    auto const length = compute.compute(data, *ptr);
    MONAD_ASSERT(length <= std::numeric_limits<uint8_t>::max());
    len = static_cast<uint8_t>(length);
    cache_node = cache;
    subtrie_min_version = calc_min_version(*ptr);
}

void ChildData::copy_old_child(Node *const old, unsigned const i)
{
    auto const index = old->to_child_index(i);
    if (old->next(index)) { // in memory, infers cached
        ptr = old->move_next(index);
    }
    auto const old_data = old->child_data_view(index);
    memcpy(&data, old_data.data(), old_data.size());
    MONAD_ASSERT(old_data.size() <= std::numeric_limits<uint8_t>::max());
    len = static_cast<uint8_t>(old_data.size());
    MONAD_ASSERT(i < 16);
    branch = static_cast<uint8_t>(i);
    offset = old->fnext(index);
    min_offsets = old->min_offsets(index);
    subtrie_min_version = old->subtrie_min_version(index);
    cache_node = ptr != nullptr;

    MONAD_ASSERT(is_valid());
}

Node::SharedPtr make_node(
    Node &from, NibblesView const path,
    std::optional<byte_string_view> const value, int64_t const version)
{
    auto const value_size =
        value.transform(&byte_string_view::size).value_or(0);
    auto node = Node::make_shared(
        calculate_node_size(
            from.number_of_children(),
            from.child_data_len(),
            value_size,
            path.data_size(),
            from.data().size()),
        from.mask,
        value,
        from.data().size(),
        path,
        version);

    // fnext, min_count, child_data_offset
    std::copy_n(
        (byte_string::pointer)&from.fnext_data,
        from.path_data() - (byte_string::pointer)&from.fnext_data,
        (byte_string::pointer)&node->fnext_data);

    // copy data and child data
    std::copy_n(
        from.data_data(),
        from.data().size() + from.child_data_len(),
        node->data_data());

    // Must initialize child pointers after copying child_data_offset
    auto const node_ptrs = node->child_next_data();
    for (size_t i = 0; i < node_ptrs.size(); ++i) {
        new (node_ptrs.data() + i) Node::SharedPtr();
    }
    auto const from_ptrs = from.child_next_data();
    for (unsigned i = 0; i < from_ptrs.size(); ++i) {
        node_ptrs[i] = std::move(from_ptrs[i]);
    }

    return node;
}

Node::SharedPtr make_node(
    uint16_t const mask, std::span<ChildData> const children,
    NibblesView const path, std::optional<byte_string_view> const value,
    size_t const data_size, int64_t const version)
{
    auto const number_of_children = static_cast<size_t>(std::popcount(mask));
    std::vector<uint16_t> child_data_offsets;
    child_data_offsets.reserve(children.size());
    uint16_t total_child_data_size = 0;
    for (auto const &child : children) {
        if (child.is_valid()) {
            MONAD_ASSERT(mask & (1u << child.branch));
            total_child_data_size += child.len;
            child_data_offsets.push_back(total_child_data_size);
        }
    }

    auto node = Node::make_shared(
        calculate_node_size(
            number_of_children,
            total_child_data_size,
            value.transform(&byte_string_view::size).value_or(0),
            path.data_size(),
            data_size),
        mask,
        value,
        data_size,
        path,
        version);

    std::copy_n(
        (byte_string_view::pointer)child_data_offsets.data(),
        child_data_offsets.size() * sizeof(uint16_t),
        reinterpret_cast<unsigned char *>(node->child_off_data().data()));

    // Must initialize child pointers after copying child_data_offset
    {
        auto const sp = node->child_next_data();
        for (size_t i = 0; i < sp.size(); ++i) {
            new (sp.data() + i) Node::SharedPtr();
        }
    }

    auto const fnext_s = node->child_fnext_data();
    auto const fast_s = node->child_min_offset_fast_data();
    auto const slow_s = node->child_min_offset_slow_data();
    auto const ver_s = node->child_min_version_data();
    auto const ptrs_s = node->child_next_data();
    for (unsigned index = 0; auto &child : children) {
        if (child.is_valid()) {
            fnext_s[index] = child.offset;
            fast_s[index] = child.min_offsets.fast;
            slow_s[index] = child.min_offsets.slow;
            ver_s[index] = child.subtrie_min_version;
            ptrs_s[index] = std::move(child.ptr);
            node->set_child_data(index, {child.data, child.len});
            ++index;
        }
    }

    return node;
}

Node::SharedPtr make_node(
    uint16_t const mask, std::span<ChildData> const children,
    NibblesView const path, std::optional<byte_string_view> const value,
    byte_string_view const data, int64_t const version)
{
    auto node = make_node(mask, children, path, value, data.size(), version);
    std::copy_n(data.data(), data.size(), node->data_data());
    return node;
}

// all children's offset are set before creating parent
// create node with at least one child
Node::SharedPtr create_node_with_children(
    Compute &comp, uint16_t const mask, std::span<ChildData> const children,
    NibblesView const path, std::optional<byte_string_view> const value,
    int64_t const version)
{
    MONAD_ASSERT(mask);
    auto const data_size =
        comp.compute_node_data_len(children, mask, path, value);
    auto node = make_node(mask, children, path, value, data_size, version);
    MONAD_ASSERT(node);
    if (data_size) {
        comp.set_node_data(node->data_data(), data_size);
    }
    return node;
}

void serialize_node_to_buffer(
    unsigned char *write_pos, unsigned bytes_to_append, Node const &node,
    uint32_t const disk_size, unsigned const offset)
{
    MONAD_ASSERT(disk_size > 0 && disk_size <= Node::max_disk_size);
    if (offset < Node::disk_size_bytes) { // serialize node disk size
        MONAD_ASSERT(bytes_to_append <= disk_size - offset);
        unsigned const written =
            std::min(bytes_to_append, Node::disk_size_bytes - offset);
        memcpy(write_pos, (unsigned char *)&disk_size + offset, written);
        bytes_to_append -= written;
        write_pos += written;
    }

    if (bytes_to_append) { // serialize node
        unsigned const offset_within_node = offset >= Node::disk_size_bytes
                                                ? offset - Node::disk_size_bytes
                                                : 0;
        memcpy(
            write_pos,
            (unsigned char *)&node + offset_within_node,
            bytes_to_append);
    }
}

int64_t calc_min_version(Node const &node)
{
    int64_t min_version = node.version;
    for (int64_t const v : node.child_min_version_data()) {
        min_version = std::min(min_version, v);
    }
    return min_version;
}

MONAD_MPT_NAMESPACE_END
