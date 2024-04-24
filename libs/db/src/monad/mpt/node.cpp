#include <monad/mpt/node.hpp>

#include <monad/async/config.hpp>
#include <monad/async/detail/scope_polyfill.hpp>
#include <monad/async/storage_pool.hpp>
#include <monad/core/assert.h>
#include <monad/core/byte_string.hpp>
#include <monad/core/keccak.h>
#include <monad/core/unaligned.hpp>
#include <monad/mem/allocators.hpp>
#include <monad/mpt/compute.hpp>
#include <monad/mpt/config.hpp>
#include <monad/mpt/nibbles_view.hpp>
#include <monad/mpt/util.hpp>

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

allocators::detail::type_raw_alloc_pair<
    std::allocator<Node>, Node::BytesAllocator>
Node::pool()
{
    static std::allocator<Node> a;
    static BytesAllocator b;
    return {a, b};
}

size_t Node::get_deallocate_count(Node *node)
{
    return node->get_mem_size();
}

Node::Node(prevent_public_construction_tag) {}

Node::Node(
    prevent_public_construction_tag, uint16_t const mask,
    std::optional<byte_string_view> value, size_t const data_size,
    NibblesView const path)
    : mask(mask)
    , data_len(static_cast<decltype(data_len)>(data_size))
    , path_nibble_index_end(path.end_nibble_)
    , value_len(static_cast<decltype(value_len)>(
          value.transform(&byte_string_view::size).value_or(0)))
{
    MONAD_DEBUG_ASSERT(
        data_size <= std::numeric_limits<decltype(data_len)>::max());
    MONAD_DEBUG_ASSERT(
        value.transform(&byte_string_view::size).value_or(0) <=
        std::numeric_limits<decltype(value_len)>::max());
    MONAD_DEBUG_ASSERT(path.begin_nibble_ <= path.end_nibble_);

    bitpacked.path_nibble_index_start = path.begin_nibble_;
    bitpacked.has_value = value.has_value();

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
    for (uint8_t index = 0; index < number_of_children(); ++index) {
        {
            UniquePtr const _{next(index)};
            (void)_;
        }
        set_next(index, nullptr);
    }
}

unsigned Node::to_child_index(unsigned const branch) const noexcept
{
    // convert the enabled i'th bit in a 16-bit mask into its corresponding
    // index location - index
    MONAD_DEBUG_ASSERT(mask & (1u << branch));
    return bitmask_index(mask, branch);
}

unsigned Node::number_of_children() const noexcept
{
    return static_cast<unsigned>(std::popcount(mask));
}

chunk_offset_t const Node::fnext(unsigned const index) const noexcept
{
    MONAD_DEBUG_ASSERT(index < number_of_children());
    return unaligned_load<chunk_offset_t>(
        fnext_data + index * sizeof(chunk_offset_t));
}

void Node::set_fnext(unsigned const index, chunk_offset_t const off) noexcept
{
    std::memcpy(
        fnext_data + index * sizeof(chunk_offset_t),
        &off,
        sizeof(chunk_offset_t));
}

unsigned char *Node::child_min_offset_fast_data() noexcept
{
    return fnext_data + number_of_children() * sizeof(file_offset_t);
}

unsigned char const *Node::child_min_offset_fast_data() const noexcept
{
    return fnext_data + number_of_children() * sizeof(file_offset_t);
}

compact_virtual_chunk_offset_t
Node::min_offset_fast(unsigned const index) noexcept
{
    return unaligned_load<compact_virtual_chunk_offset_t>(
        child_min_offset_fast_data() +
        index * sizeof(compact_virtual_chunk_offset_t));
}

void Node::set_min_offset_fast(
    unsigned const index, compact_virtual_chunk_offset_t const offset) noexcept
{
    std::memcpy(
        child_min_offset_fast_data() +
            index * sizeof(compact_virtual_chunk_offset_t),
        &offset,
        sizeof(compact_virtual_chunk_offset_t));
}

unsigned char *Node::child_min_offset_slow_data() noexcept
{
    return child_min_offset_fast_data() +
           number_of_children() * sizeof(compact_virtual_chunk_offset_t);
}

unsigned char const *Node::child_min_offset_slow_data() const noexcept
{
    return child_min_offset_fast_data() +
           number_of_children() * sizeof(compact_virtual_chunk_offset_t);
}

compact_virtual_chunk_offset_t
Node::min_offset_slow(unsigned const index) noexcept
{
    return unaligned_load<compact_virtual_chunk_offset_t>(
        child_min_offset_slow_data() +
        index * sizeof(compact_virtual_chunk_offset_t));
}

void Node::set_min_offset_slow(
    unsigned const index, compact_virtual_chunk_offset_t const offset) noexcept
{
    std::memcpy(
        child_min_offset_slow_data() +
            index * sizeof(compact_virtual_chunk_offset_t),
        &offset,
        sizeof(compact_virtual_chunk_offset_t));
}

unsigned char *Node::child_off_data() noexcept
{
    return child_min_offset_slow_data() +
           number_of_children() * sizeof(uint32_t);
}

unsigned char const *Node::child_off_data() const noexcept
{
    return child_min_offset_slow_data() +
           number_of_children() * sizeof(uint32_t);
}

uint16_t Node::child_data_offset(unsigned const index) const noexcept
{
    MONAD_DEBUG_ASSERT(index <= number_of_children());
    if (index == 0) {
        return 0;
    }
    return unaligned_load<uint16_t>(
        child_off_data() + (index - 1) * sizeof(uint16_t));
}

unsigned Node::child_data_len(unsigned const index)
{
    return child_data_offset(index + 1) - child_data_offset(index);
}

unsigned Node::child_data_len()
{
    return child_data_offset(number_of_children()) - child_data_offset(0);
}

unsigned char *Node::path_data() noexcept
{
    return child_off_data() + number_of_children() * sizeof(uint16_t);
}

unsigned char const *Node::path_data() const noexcept
{
    return child_off_data() + number_of_children() * sizeof(uint16_t);
}

unsigned Node::path_nibbles_len() const noexcept
{
    MONAD_DEBUG_ASSERT(
        bitpacked.path_nibble_index_start <= path_nibble_index_end);
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
    MONAD_DEBUG_ASSERT(has_value());
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
    return {data_data(), data_len};
}

unsigned char *Node::child_data() noexcept
{
    return data_data() + data_len;
}

unsigned char const *Node::child_data() const noexcept
{
    return data_data() + data_len;
}

byte_string_view Node::child_data_view(unsigned const index) noexcept
{
    MONAD_DEBUG_ASSERT(index < number_of_children());
    return byte_string_view{
        child_data() + child_data_offset(index),
        static_cast<size_t>(child_data_len(index))};
}

unsigned char *Node::child_data(unsigned const index) noexcept
{
    MONAD_DEBUG_ASSERT(index < number_of_children());
    return child_data() + child_data_offset(index);
}

void Node::set_child_data(unsigned const index, byte_string_view data) noexcept
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

Node *Node::next(size_t const index) noexcept
{
    return unaligned_load<Node *>(next_data() + index * sizeof(Node *));
}

Node const *Node::next(size_t const index) const noexcept
{
    return unaligned_load<Node *>(next_data() + index * sizeof(Node *));
}

void Node::set_next(unsigned const index, Node *const node) noexcept
{
    node ? memcpy(next_data() + index * sizeof(Node *), &node, sizeof(Node *))
         : memset(next_data() + index * sizeof(Node *), 0, sizeof(Node *));
}

Node::UniquePtr Node::next_ptr(unsigned const index) noexcept
{
    Node *p = next(index);
    set_next(index, nullptr);
    return UniquePtr{p};
}

unsigned Node::get_mem_size() noexcept
{
    auto const *const end = next_data() + sizeof(Node *) * number_of_children();
    MONAD_DEBUG_ASSERT(end >= (unsigned char *)this);
    auto const mem_size = static_cast<unsigned>(end - (unsigned char *)this);
    MONAD_DEBUG_ASSERT(mem_size <= Node::max_size);
    return mem_size;
}

uint32_t Node::get_disk_size() noexcept
{
    MONAD_DEBUG_ASSERT(next_data() >= (unsigned char *)this);
    auto const disk_size =
        static_cast<uint32_t>(next_data() - (unsigned char *)this);
    MONAD_DEBUG_ASSERT(disk_size <= Node::max_disk_size);
    return disk_size;
}

bool ChildData::is_valid() const
{
    return branch != INVALID_BRANCH;
}

void ChildData::erase()
{
    branch = INVALID_BRANCH;
}

void ChildData::finalize(Node &node, Compute &compute, bool const cache)
{
    MONAD_DEBUG_ASSERT(is_valid());
    ptr = &node;
    auto const length = compute.compute(data, ptr);
    MONAD_DEBUG_ASSERT(length <= std::numeric_limits<uint8_t>::max());
    len = static_cast<uint8_t>(length);
    cache_node = cache;
}

void ChildData::copy_old_child(Node *const old, unsigned const i)
{
    auto const index = old->to_child_index(i);
    if (old->next(index)) { // in memory, infers cached
        ptr = old->next_ptr(index).release();
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
    cache_node = true;

    MONAD_DEBUG_ASSERT(is_valid());
}

Node::UniquePtr make_node(
    Node &from, NibblesView const path,
    std::optional<byte_string_view> const value)
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
        path);

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

    node->disk_size = node->get_disk_size();
    return node;
}

Node::UniquePtr make_node(
    uint16_t const mask, std::span<ChildData> const children,
    NibblesView const path, std::optional<byte_string_view> const value,
    size_t const data_size)
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
        path);

    std::copy_n(
        (byte_string_view::pointer)child_data_offsets.data(),
        child_data_offsets.size() * sizeof(uint16_t),
        node->child_off_data());

    for (unsigned index = 0; auto const &child : children) {
        if (child.is_valid()) {
            node->set_fnext(index, child.offset);
            node->set_min_offset_fast(index, child.min_offset_fast);
            node->set_min_offset_slow(index, child.min_offset_slow);
            node->set_next(index, child.ptr);
            node->set_child_data(index, {child.data, child.len});
            ++index;
        }
    }

    node->disk_size = node->get_disk_size();
    return node;
}

Node::UniquePtr make_node(
    uint16_t const mask, std::span<ChildData> const children,
    NibblesView const path, std::optional<byte_string_view> const value,
    byte_string_view const data)
{
    auto node = make_node(mask, children, path, value, data.size());
    std::copy_n(data.data(), data.size(), node->data_data());
    return node;
}

// all children's offset are set before creating parent
// create node with at least one child
Node *create_node_with_children(
    Compute &comp, uint16_t const mask, std::span<ChildData> children,
    NibblesView const path, std::optional<byte_string_view> const value)
{
    MONAD_ASSERT(mask);
    auto const data_size = comp.compute_len(children, mask, path, value);
    auto node = make_node(mask, children, path, value, data_size);
    MONAD_DEBUG_ASSERT(node);
    if (data_size) {
        comp.compute_branch(node->data_data(), node.get());
    }
    return node.release();
}

void serialize_node_to_buffer(
    unsigned char *const write_pos, unsigned const bytes_to_append,
    Node const &node, unsigned const offset)
{
    MONAD_ASSERT(node.disk_size > 0 && node.disk_size <= Node::max_disk_size);
    MONAD_ASSERT(bytes_to_append <= node.disk_size - offset);
    memcpy(write_pos, (unsigned char *)&node + offset, bytes_to_append);
}

Node::UniquePtr
deserialize_node_from_buffer(unsigned char const *read_pos, size_t max_bytes)
{
    for (size_t n = 0; n < max_bytes; n += 64) {
        __builtin_prefetch(read_pos + n, 0, 0);
    }
    auto const mask = unaligned_load<uint16_t>(read_pos);
    auto const number_of_children = static_cast<unsigned>(std::popcount(mask));
    auto const disk_size =
        unaligned_load<uint32_t>(read_pos + offsetof(Node, disk_size));
    MONAD_ASSERT(disk_size <= max_bytes);
    auto const alloc_size =
        static_cast<uint32_t>(disk_size + number_of_children * sizeof(Node *));
    MONAD_ASSERT(disk_size > 0 && disk_size <= Node::max_disk_size);
    auto node = Node::make(alloc_size);
    std::copy_n(read_pos, disk_size, (unsigned char *)node.get());
    std::memset(node->next_data(), 0, number_of_children * sizeof(Node *));
    return node;
}

Node *read_node_blocking(
    MONAD_ASYNC_NAMESPACE::storage_pool &pool, chunk_offset_t node_offset)
{
    MONAD_DEBUG_ASSERT(
        node_offset.spare <=
        round_up_align<DISK_PAGE_BITS>(Node::max_disk_size));
    // spare bits are number of pages needed to load node
    unsigned const num_pages_to_load_node =
        node_disk_pages_spare_15{node_offset}.to_pages();
    unsigned const bytes_to_read = num_pages_to_load_node << DISK_PAGE_BITS;
    file_offset_t const rd_offset =
        round_down_align<DISK_PAGE_BITS>(node_offset.offset);
    uint16_t const buffer_off = uint16_t(node_offset.offset - rd_offset);
    auto *buffer =
        (unsigned char *)aligned_alloc(DISK_PAGE_SIZE, bytes_to_read);
    auto unbuffer = make_scope_exit([buffer]() noexcept { ::free(buffer); });

    auto chunk = pool.activate_chunk(pool.seq, node_offset.id);
    auto fd = chunk->read_fd();
    ssize_t const bytes_read = pread(
        fd.first,
        buffer,
        bytes_to_read,
        static_cast<off_t>(fd.second + rd_offset));
    if (bytes_read < 0) {
        fprintf(
            stderr,
            "FATAL: pread(%u, %llu) failed with '%s'\n",
            bytes_to_read,
            rd_offset,
            strerror(errno));
    }
    return deserialize_node_from_buffer(
               buffer + buffer_off, size_t(bytes_read) - buffer_off)
        .release();
}

MONAD_MPT_NAMESPACE_END
