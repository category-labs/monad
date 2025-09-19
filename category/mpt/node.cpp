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

#include <category/async/config.hpp>
#include <category/async/storage_pool.hpp>
#include <category/core/assert.h>
#include <category/core/byte_string.hpp>
#include <category/core/keccak.h>
#include <category/core/mem/allocators.hpp>
#include <category/core/unaligned.hpp>
#include <category/mpt/compute.hpp>
#include <category/mpt/config.hpp>
#include <category/mpt/nibbles_view.hpp>
#include <category/mpt/util.hpp>

#include <algorithm>
#include <bit>
#include <cassert>
#include <cerrno>
#include <cstddef>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <limits>
#include <memory>
#include <optional>
#include <span>
#include <unistd.h>
#include <utility>
#include <vector>

MONAD_MPT_NAMESPACE_BEGIN

Node::Node(prevent_public_construction_tag) {}

NodeBase::NodeBase(
    prevent_public_construction_tag, uint16_t const mask,
    std::optional<byte_string_view> value, size_t const data_size,
    NibblesView const path, int64_t const version)
    : mask(mask)
    , path_nibble_index_end(path.end_nibble_)
    , value_len(static_cast<decltype(value_len)>(
          value.transform(&byte_string_view::size).value_or(0)))
    , version(version)
{
    MONAD_DEBUG_ASSERT(
        value.transform(&byte_string_view::size).value_or(0) <=
        std::numeric_limits<decltype(value_len)>::max());
    MONAD_DEBUG_ASSERT(path.begin_nibble_ <= path.end_nibble_);
    bitpacked.path_nibble_index_start = path.begin_nibble_;
    bitpacked.has_value = value.has_value();

    MONAD_ASSERT(data_size <= Node::max_data_len);
    bitpacked.data_len = static_cast<uint8_t>(data_size & Node::max_data_len);

    if (path.data_size()) {
        MONAD_DEBUG_ASSERT(path.data_);
        std::copy_n(path.data_, path.data_size(), path_data());
    }

    if (value_len) {
        std::copy_n(value.value().data(), value.value().size(), value_data());
    }
}

Node::~Node()
{
    for (unsigned index = 0; index < number_of_children(); ++index) {
        move_next(index).reset();
    }
}

unsigned NodeBase::to_child_index(unsigned const branch) const noexcept
{
    // convert the enabled i'th bit in a 16-bit mask into its corresponding
    // index location - index
    MONAD_DEBUG_ASSERT(mask & (1u << branch));
    return bitmask_index(mask, branch);
}

unsigned NodeBase::number_of_children() const noexcept
{
    return static_cast<unsigned>(std::popcount(mask));
}

chunk_offset_t const NodeBase::fnext(unsigned const index) const noexcept
{
    MONAD_DEBUG_ASSERT(index < number_of_children());
    return unaligned_load<chunk_offset_t>(
        fnext_data + index * sizeof(chunk_offset_t));
}

void NodeBase::set_fnext(
    unsigned const index, chunk_offset_t const off) noexcept
{
    std::memcpy(
        fnext_data + index * sizeof(chunk_offset_t),
        &off,
        sizeof(chunk_offset_t));
}

unsigned char *NodeBase::child_min_offset_fast_data() noexcept
{
    return fnext_data + number_of_children() * sizeof(file_offset_t);
}

unsigned char const *NodeBase::child_min_offset_fast_data() const noexcept
{
    return fnext_data + number_of_children() * sizeof(file_offset_t);
}

compact_virtual_chunk_offset_t
NodeBase::min_offset_fast(unsigned const index) const noexcept
{
    return unaligned_load<compact_virtual_chunk_offset_t>(
        child_min_offset_fast_data() +
        index * sizeof(compact_virtual_chunk_offset_t));
}

void NodeBase::set_min_offset_fast(
    unsigned const index, compact_virtual_chunk_offset_t const offset) noexcept
{
    std::memcpy(
        child_min_offset_fast_data() +
            index * sizeof(compact_virtual_chunk_offset_t),
        &offset,
        sizeof(compact_virtual_chunk_offset_t));
}

unsigned char *NodeBase::child_min_offset_slow_data() noexcept
{
    return child_min_offset_fast_data() +
           number_of_children() * sizeof(compact_virtual_chunk_offset_t);
}

unsigned char const *NodeBase::child_min_offset_slow_data() const noexcept
{
    return child_min_offset_fast_data() +
           number_of_children() * sizeof(compact_virtual_chunk_offset_t);
}

compact_virtual_chunk_offset_t
NodeBase::min_offset_slow(unsigned const index) const noexcept
{
    return unaligned_load<compact_virtual_chunk_offset_t>(
        child_min_offset_slow_data() +
        index * sizeof(compact_virtual_chunk_offset_t));
}

void NodeBase::set_min_offset_slow(
    unsigned const index, compact_virtual_chunk_offset_t const offset) noexcept
{
    std::memcpy(
        child_min_offset_slow_data() +
            index * sizeof(compact_virtual_chunk_offset_t),
        &offset,
        sizeof(compact_virtual_chunk_offset_t));
}

unsigned char *NodeBase::child_min_version_data() noexcept
{
    return child_min_offset_slow_data() +
           number_of_children() * sizeof(compact_virtual_chunk_offset_t);
}

unsigned char const *NodeBase::child_min_version_data() const noexcept
{
    return child_min_offset_slow_data() +
           number_of_children() * sizeof(compact_virtual_chunk_offset_t);
}

int64_t NodeBase::subtrie_min_version(unsigned const index) const noexcept
{
    return unaligned_load<int64_t>(
        child_min_version_data() + index * sizeof(int64_t));
}

void NodeBase::set_subtrie_min_version(
    unsigned const index, int64_t const min_version) noexcept
{
    std::memcpy(
        child_min_version_data() + index * sizeof(int64_t),
        &min_version,
        sizeof(int64_t));
}

unsigned char *NodeBase::child_off_data() noexcept
{
    return child_min_version_data() + number_of_children() * sizeof(int64_t);
}

unsigned char const *NodeBase::child_off_data() const noexcept
{
    return child_min_version_data() + number_of_children() * sizeof(int64_t);
}

uint16_t NodeBase::child_data_offset(unsigned const index) const noexcept
{
    MONAD_DEBUG_ASSERT(index <= number_of_children());
    if (index == 0) {
        return 0;
    }
    return unaligned_load<uint16_t>(
        child_off_data() + (index - 1) * sizeof(uint16_t));
}

unsigned NodeBase::child_data_len(unsigned const index) const
{
    return child_data_offset(index + 1) - child_data_offset(index);
}

unsigned NodeBase::child_data_len()
{
    return child_data_offset(number_of_children()) - child_data_offset(0);
}

unsigned char *NodeBase::path_data() noexcept
{
    return child_off_data() + number_of_children() * sizeof(uint16_t);
}

unsigned char const *NodeBase::path_data() const noexcept
{
    return child_off_data() + number_of_children() * sizeof(uint16_t);
}

unsigned NodeBase::path_nibbles_len() const noexcept
{
    MONAD_DEBUG_ASSERT(
        bitpacked.path_nibble_index_start <= path_nibble_index_end);
    return path_nibble_index_end - bitpacked.path_nibble_index_start;
}

bool NodeBase::has_path() const noexcept
{
    return path_nibbles_len() > 0;
}

unsigned NodeBase::path_bytes() const noexcept
{
    return (path_nibble_index_end + 1) / 2;
}

NibblesView NodeBase::path_nibble_view() const noexcept
{
    return NibblesView{
        bitpacked.path_nibble_index_start, path_nibble_index_end, path_data()};
}

unsigned NodeBase::path_start_nibble() const noexcept
{
    return bitpacked.path_nibble_index_start;
}

unsigned char *NodeBase::value_data() noexcept
{
    return path_data() + path_bytes();
}

unsigned char const *NodeBase::value_data() const noexcept
{
    return path_data() + path_bytes();
}

bool NodeBase::has_value() const noexcept
{
    return bitpacked.has_value;
}

byte_string_view NodeBase::value() const noexcept
{
    MONAD_DEBUG_ASSERT(has_value());
    return {value_data(), value_len};
}

std::optional<byte_string_view> NodeBase::opt_value() const noexcept
{
    if (has_value()) {
        return value();
    }
    return std::nullopt;
}

unsigned char *NodeBase::data_data() noexcept
{
    return value_data() + value_len;
}

unsigned char const *NodeBase::data_data() const noexcept
{
    return value_data() + value_len;
}

byte_string_view NodeBase::data() const noexcept
{
    return {data_data(), bitpacked.data_len};
}

unsigned char *NodeBase::child_data() noexcept
{
    return data_data() + bitpacked.data_len;
}

unsigned char const *NodeBase::child_data() const noexcept
{
    return data_data() + bitpacked.data_len;
}

byte_string_view NodeBase::child_data_view(unsigned const index) const noexcept
{
    MONAD_DEBUG_ASSERT(index < number_of_children());
    return byte_string_view{
        child_data() + child_data_offset(index),
        static_cast<size_t>(child_data_len(index))};
}

unsigned char *NodeBase::child_data(unsigned const index) noexcept
{
    MONAD_DEBUG_ASSERT(index < number_of_children());
    return child_data() + child_data_offset(index);
}

void NodeBase::set_child_data(
    unsigned const index, byte_string_view data) noexcept
{
    // called after data_off array is calculated
    std::memcpy(child_data(index), data.data(), data.size());
}

unsigned char *NodeBase::next_data() noexcept
{
    return child_data() + child_data_offset(number_of_children());
}

unsigned char const *NodeBase::next_data() const noexcept
{
    return child_data() + child_data_offset(number_of_children());
}

void *NodeBase::next(size_t const index) const noexcept
{
    return unaligned_load<void *>(next_data() + index * sizeof(Node *));
}

void NodeBase::set_next(unsigned const index, void *const ptr) noexcept
{
    ptr ? memcpy(next_data() + index * sizeof(Node *), &ptr, sizeof(void *))
        : memset(next_data() + index * sizeof(Node *), 0, sizeof(void *));
}

void *NodeBase::move_next(unsigned const index) noexcept
{
    auto const p = next(index);
    set_next(index, nullptr);
    return p;
}

unsigned NodeBase::get_mem_size() const noexcept
{
    auto const *const end = next_data() + sizeof(Node *) * number_of_children();
    MONAD_DEBUG_ASSERT(end >= (unsigned char *)this);
    auto const mem_size = static_cast<unsigned>(end - (unsigned char *)this);
    MONAD_DEBUG_ASSERT(mem_size <= NodeBase::max_size);
    return mem_size;
}

uint32_t NodeBase::get_disk_size() const noexcept
{
    MONAD_DEBUG_ASSERT(next_data() >= (unsigned char *)this);
    auto const node_disk_size =
        static_cast<uint32_t>(next_data() - (unsigned char *)this);
    uint32_t const total_disk_size = node_disk_size + NodeBase::disk_size_bytes;
    MONAD_DEBUG_ASSERT(total_disk_size <= NodeBase::max_disk_size);
    return total_disk_size;
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
    Node::UniquePtr node, Compute &compute, bool const cache)
{
    MONAD_DEBUG_ASSERT(is_valid());
    ptr = std::move(node);
    auto const length = compute.compute(data, ptr.get());
    MONAD_DEBUG_ASSERT(length <= std::numeric_limits<uint8_t>::max());
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
    MONAD_DEBUG_ASSERT(old_data.size() <= std::numeric_limits<uint8_t>::max());
    len = static_cast<uint8_t>(old_data.size());
    MONAD_DEBUG_ASSERT(i < 16);
    branch = static_cast<uint8_t>(i);
    offset = old->fnext(index);
    min_offset_fast = old->min_offset_fast(index);
    min_offset_slow = old->min_offset_slow(index);
    subtrie_min_version = old->subtrie_min_version(index);
    cache_node = ptr != nullptr;

    MONAD_DEBUG_ASSERT(is_valid());
}

Node::UniquePtr make_node(
    Node &from, NibblesView const path,
    std::optional<byte_string_view> const value, int64_t const version)
{
    auto const value_size =
        value.transform(&byte_string_view::size).value_or(0);
    auto node = Node::make(
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

    // move next ptrs to new node, invalidating old pointers
    if (from.number_of_children()) {
        auto const next_size = from.number_of_children() * sizeof(Node *);
        std::copy_n(from.next_data(), next_size, node->next_data());
        std::memset(from.next_data(), 0, next_size);
    }

    return node;
}

Node::UniquePtr make_node(
    uint16_t const mask, std::span<ChildData> const children,
    NibblesView const path, std::optional<byte_string_view> const value,
    size_t const data_size, int64_t const version)
{
    MONAD_DEBUG_ASSERT(data_size <= KECCAK256_SIZE);
    if (value.has_value()) {
        MONAD_DEBUG_ASSERT(
            value->size() <=
            std::numeric_limits<decltype(Node::value_len)>::max());
    }
    for (size_t i = 0; i < 16; ++i) {
        MONAD_DEBUG_ASSERT(
            !std::ranges::contains(children, i, &ChildData::branch) ||
            (mask & (1u << i)));
    }

    auto const number_of_children = static_cast<size_t>(std::popcount(mask));
    std::vector<uint16_t> child_data_offsets;
    child_data_offsets.reserve(children.size());
    uint16_t total_child_data_size = 0;
    for (auto const &child : children) {
        if (child.is_valid()) {
            total_child_data_size += child.len;
            child_data_offsets.push_back(total_child_data_size);
        }
    }

    auto node = Node::make(
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
        node->child_off_data());

    for (unsigned index = 0; auto &child : children) {
        if (child.is_valid()) {
            node->set_fnext(index, child.offset);
            node->set_min_offset_fast(index, child.min_offset_fast);
            node->set_min_offset_slow(index, child.min_offset_slow);
            node->set_subtrie_min_version(index, child.subtrie_min_version);
            node->set_next(index, std::move(child.ptr));
            node->set_child_data(index, {child.data, child.len});
            ++index;
        }
    }

    return node;
}

Node::UniquePtr make_node(
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
Node::UniquePtr create_node_with_children(
    Compute &comp, uint16_t const mask, std::span<ChildData> const children,
    NibblesView const path, std::optional<byte_string_view> const value,
    int64_t const version)
{
    MONAD_ASSERT(mask);
    auto const data_size = comp.compute_len(children, mask, path, value);
    auto node = make_node(mask, children, path, value, data_size, version);
    MONAD_DEBUG_ASSERT(node);
    if (data_size) {
        comp.compute_branch(node->data_data(), node.get());
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
    for (unsigned i = 0; i < node.number_of_children(); ++i) {
        min_version = std::min(min_version, node.subtrie_min_version(i));
    }
    return min_version;
}

MONAD_MPT_NAMESPACE_END
