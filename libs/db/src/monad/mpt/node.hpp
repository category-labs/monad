#pragma once

#include <monad/async/storage_pool.hpp>
#include <monad/core/byte_string.hpp>
#include <monad/core/endian.hpp> // NOLINT
#include <monad/core/keccak.h>
#include <monad/core/math.hpp>
#include <monad/mem/allocators.hpp>
#include <monad/mpt/detail/unsigned_20.hpp>
#include <monad/mpt/util.hpp>
#include <monad/rlp/encode.hpp>

#include <cstdint>
#include <optional>
#include <span>

MONAD_MPT_NAMESPACE_BEGIN

struct Compute;
class NibblesView;

struct node_disk_pages_spare_15
{
    struct spare_type_15
    {
        uint16_t count : 10;
        uint16_t shift : 5;
        uint16_t reserved0_ : 1;
    };

    union spare_dual
    {
        spare_type_15 spare;
        uint16_t value;

        constexpr spare_dual(uint16_t v)
            : value(v)
        {
        }
    } value;

    static constexpr unsigned count_bits = 10;
    static constexpr size_t max_count = (1UL << 10) - 1;
    static constexpr uint16_t max_shift = (1U << 5) - 1;

    explicit constexpr node_disk_pages_spare_15(chunk_offset_t const offset)
        : value(static_cast<uint16_t>(offset.spare))
    {
    }

    explicit constexpr node_disk_pages_spare_15(unsigned const pages)
        : value{0}
    {
        unsigned const exp = pages >> count_bits;
        auto shift = static_cast<uint16_t>(
            std::numeric_limits<decltype(exp)>::digits - std::countl_zero(exp));
        auto count = (pages >> shift) + (0 != (pages & ((1u << shift) - 1)));
        if (count > max_count) {
            count >>= 1;
            shift += 1;
        }
        MONAD_ASSERT(count <= max_count);
        MONAD_ASSERT(shift <= max_shift);
        value.spare.count = count & max_count;
        value.spare.shift = shift & max_shift;
        MONAD_ASSERT(to_pages() >= pages);
    }

    constexpr unsigned to_pages() const noexcept
    {
        return static_cast<unsigned>(value.spare.count) << value.spare.shift;
    }

    // conversion to uint16_t
    explicit constexpr operator uint16_t() const noexcept
    {
        return value.value;
    }
};

/* A note on generic trie

In Ethereum merkle patricia trie:
- Node is a extension if path len > 0, it only has one child, a branch node
- Node is a branch if mask > 0 && path len == 0, branch can have leaf value
- Node is a leaf node if it has no child

In generic trie, a node can have dual identity of ext and branch node, and
branch node can have vt (value) and be a leaf node at the same time. Branch node
with leaf data can have 1 child or more.
- A node with non-empty path is either an ext node or a leaf node
- A leaf node has has_value = true, however not necessarily value_len > 0
- A branch node with leaf can mean it's the end of an internal trie, making
itself also the root of the trie underneath, for example a leaf of an
account trie, where the account has an underlying storage trie. It can also
simply mean it's a branch node inside an internal trie, for example a branch
node with value in a receipt trie (var key length). Such branch node with leaf
will cache an intemediate hash inline.

Similar like a merkle patricia trie, each node's data is computed from its child
nodes data. Triedb is divided into different sections, indexed by unique
prefixes (i.e. sections for accounts, storages, receipts, etc.), node data is
defined differently in each section, and we leave the actual computation to the
`class Compute` to handle it.
We store node data to its parent's storage to avoid an extra read of child node
to retrieve child data.
*/

class Node
{
    struct prevent_public_construction_tag
    {
    };

public:
    static constexpr size_t max_number_of_children = 16;
    static constexpr uint8_t max_data_len = (1U << 6) - 1;
    static constexpr size_t max_disk_size =
        256 * 1024 * 1024; // 256mb, same as storage chunk size
    static constexpr unsigned disk_size_bytes = sizeof(uint32_t);
    static constexpr size_t max_size =
        max_disk_size + max_number_of_children * KECCAK256_SIZE;
    using BytesAllocator = allocators::malloc_free_allocator<std::byte>;

    static allocators::detail::type_raw_alloc_pair<
        std::allocator<Node>, BytesAllocator>
    pool();
    static size_t get_deallocate_count(Node *);

    using Deleter = allocators::unique_ptr_aliasing_allocator_deleter<
        std::allocator<Node>, BytesAllocator, &Node::pool,
        &Node::get_deallocate_count>;
    using UniquePtr = std::unique_ptr<Node, Deleter>;

    /* 16-bit mask for children */
    uint16_t mask{0};

    struct bitpacked_storage_t
    {
        /* does node have a value, value_len is not necessarily positive */
        bool has_value : 1 {false};
        bool path_nibble_index_start : 1 {false};
        /* size (in byte) of intermediate cache for branch hash */
        uint8_t data_len : 6 {0};
    } bitpacked{0};

    static_assert(sizeof(bitpacked) == 1);

    uint8_t path_nibble_index_end{0};
    /* size (in byte) of user-passed leaf data */
    uint32_t value_len{0};
    /* A note on definition of node version:
    version(leaf node) corresponds to the block number when it was
    last updated.
    version(interior node) >= max(version of the leaf nodes under its prefix),
    it is greater than only when the latest update in the subtrie contains only
    deletions. */
    int64_t version{0};

#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wpedantic"
    unsigned char fnext_data[0];
#pragma GCC diagnostic pop

    /* Member funcs and data layout that exceeds node struct size is organized
    as below:
    * `number_of_children()` is the number of children the node has and equals
    std::popcount(mask)
    * `fnext` array: size-n array storing children's on-disk offsets
    * `data_offset` array: size-n array each stores a specific child data's
    starting offset
    * `path`: a few bytes for relative path, size depends on
    path_nibble_index_start, path_nibble_index_end
    * `value`: user-passed leaf data of value_len bytes
    * `data`: intermediate hash cached for a implicit branch node, which
    exists in leaf nodes that have child.
    * `data_arr`: concatenated data bytes for all children
    * `next` array: size-n array storing children's mem pointers
    */

    // TODO:
    // 1. get rid of data_off_arr, and store child data bytes as rlp encoded
    // bytes
    // 2. children data_arr can be stored out of line or we reuse nodes instead
    // of allocating new ones when node size remains the same, as most of the
    // time only one child out of multiple is updated, and other children's data
    // remains unchanged, storing inline requires copying them all, storing data
    // out of line allows us to transfer ownership of data array from old node
    // to new one, also help to keep allocated size as small as possible.

    template <class... Args>
    static UniquePtr make(size_t bytes, Args &&...args)
    {
        MONAD_DEBUG_ASSERT(bytes <= Node::max_size);
        return allocators::allocate_aliasing_unique<
            std::allocator<Node>,
            BytesAllocator,
            &pool,
            &get_deallocate_count>(
            bytes,
            prevent_public_construction_tag{},
            std::forward<Args>(args)...);
    }

    Node(prevent_public_construction_tag);
    Node(
        prevent_public_construction_tag, uint16_t mask,
        std::optional<byte_string_view> value, size_t data_size,
        NibblesView path, int64_t version);
    Node(Node const &) = delete;
    Node(Node &&) = default;
    ~Node();

    unsigned to_child_index(unsigned branch) const noexcept;

    unsigned number_of_children() const noexcept;

    //! fnext array that stores physical chunk offset of each child
    chunk_offset_t const fnext(unsigned index) const noexcept;
    void set_fnext(unsigned index, chunk_offset_t) noexcept;

    //! fastlist min_offset array
    unsigned char *child_min_offset_fast_data() noexcept;
    unsigned char const *child_min_offset_fast_data() const noexcept;
    compact_virtual_chunk_offset_t
    min_offset_fast(unsigned index) const noexcept;
    void set_min_offset_fast(
        unsigned index, compact_virtual_chunk_offset_t) noexcept;
    //! slowlist min_offset array
    unsigned char *child_min_offset_slow_data() noexcept;
    unsigned char const *child_min_offset_slow_data() const noexcept;
    compact_virtual_chunk_offset_t
    min_offset_slow(unsigned index) const noexcept;
    void set_min_offset_slow(
        unsigned index, compact_virtual_chunk_offset_t) noexcept;

    //! subtrie min version array
    unsigned char *child_min_version_data() noexcept;
    unsigned char const *child_min_version_data() const noexcept;
    int64_t subtrie_min_version(unsigned index) const noexcept;
    void set_subtrie_min_version(unsigned index, int64_t version) noexcept;

    //! data_offset array
    unsigned char *child_off_data() noexcept;
    unsigned char const *child_off_data() const noexcept;
    uint16_t child_data_offset(unsigned index) const noexcept;

    unsigned child_data_len(unsigned index) const;
    unsigned child_data_len();

    //! path
    unsigned char *path_data() noexcept;
    unsigned char const *path_data() const noexcept;
    unsigned path_nibbles_len() const noexcept;
    bool has_path() const noexcept;
    unsigned path_bytes() const noexcept;
    NibblesView path_nibble_view() const noexcept;
    unsigned path_start_nibble() const noexcept;

    //! value
    unsigned char *value_data() noexcept;
    unsigned char const *value_data() const noexcept;
    bool has_value() const noexcept;
    byte_string_view value() const noexcept;
    std::optional<byte_string_view> opt_value() const noexcept;

    //! data
    unsigned char *data_data() noexcept;
    unsigned char const *data_data() const noexcept;
    byte_string_view data() const noexcept;

    //! child data
    unsigned char *child_data() noexcept;
    unsigned char const *child_data() const noexcept;
    byte_string_view child_data_view(unsigned index) const noexcept;
    unsigned char *child_data(unsigned index) noexcept;
    void set_child_data(unsigned index, byte_string_view data) noexcept;

    //! next pointers
    unsigned char *next_data() noexcept;
    unsigned char const *next_data() const noexcept;
    Node *next(size_t index) noexcept;
    Node const *next(size_t index) const noexcept;
    void set_next(unsigned index, Node::UniquePtr) noexcept;
    UniquePtr move_next(unsigned index) noexcept;

    //! node size in memory
    unsigned get_mem_size() const noexcept;
    uint32_t get_disk_size() const noexcept;
};

static_assert(std::is_standard_layout_v<Node>, "required by offsetof");
static_assert(sizeof(Node) == 16);
static_assert(alignof(Node) == 8);

// ChildData is for temporarily holding a child's info, including child ptr,
// file offset and hash data, in the update recursion.
struct ChildData
{
    Node::UniquePtr ptr{nullptr};
    chunk_offset_t offset{INVALID_OFFSET}; // physical offsets
    unsigned char data[32] = {0};
    int64_t subtrie_min_version{std::numeric_limits<int64_t>::max()};
    compact_virtual_chunk_offset_t min_offset_fast{
        INVALID_COMPACT_VIRTUAL_OFFSET};
    compact_virtual_chunk_offset_t min_offset_slow{
        INVALID_COMPACT_VIRTUAL_OFFSET};

    uint8_t branch{INVALID_BRANCH};
    uint8_t len{0};
    bool cache_node{true}; // attach ptr to parent if cache, free otherwise

    bool is_valid() const;
    void erase();
    void finalize(Node::UniquePtr, Compute &, bool cache);
    void copy_old_child(Node *old, unsigned i);
};

static_assert(sizeof(ChildData) == 72);
static_assert(alignof(ChildData) == 8);

constexpr size_t calculate_node_size(
    size_t const number_of_children, size_t const total_child_data_size,
    size_t const value_size, size_t const path_size,
    size_t const data_size) noexcept
{
    return sizeof(Node) +
           (sizeof(uint16_t) // child data offset
            + sizeof(compact_virtual_chunk_offset_t) * 2 // min truncated offset
            + sizeof(int64_t) // subtrie min versions
            + sizeof(chunk_offset_t) + sizeof(Node *)) *
               number_of_children +
           total_child_data_size + value_size + path_size + data_size;
}

// Maximum value size that can be stored in a leaf node.  This is calculated by
// taking the maximum possible node size and subtracting the overhead of the
// Node metadata. We use KECCAK256_SIZE for the path length since the state trie
// is our deepest trie in practice.
constexpr size_t MAX_VALUE_LEN_OF_LEAF =
    Node::max_disk_size -
    calculate_node_size(
        0 /* number_of_children */, 0 /* child_data_size */, 0 /* value_size */,
        KECCAK256_SIZE /* path_size */, KECCAK256_SIZE /* data_size*/);

Node::UniquePtr make_node(
    Node &from, NibblesView path, std::optional<byte_string_view> value,
    int64_t version);

Node::UniquePtr make_node(
    uint16_t mask, std::span<ChildData>, NibblesView path,
    std::optional<byte_string_view> value, size_t data_size, int64_t version);

Node::UniquePtr make_node(
    uint16_t mask, std::span<ChildData>, NibblesView path,
    std::optional<byte_string_view> value, byte_string_view data,
    int64_t version);

// create node: either branch/extension, with or without leaf
Node::UniquePtr create_node_with_children(
    Compute &, uint16_t mask, std::span<ChildData> children, NibblesView path,
    std::optional<byte_string_view> value, int64_t version);

void serialize_node_to_buffer(
    unsigned char *write_pos, unsigned bytes_to_write, Node const &,
    uint32_t disk_size, unsigned offset = 0);

Node::UniquePtr
deserialize_node_from_buffer(unsigned char const *read_pos, size_t max_bytes);

Node::UniquePtr copy_node(Node const *);

int64_t calc_min_version(Node const &);

// Iterate over the children of a node returning the index and the branch
// Usage: for (auto const [index, branch] : NodeChildrenRange(node.mask)) {...}
class NodeChildrenRange
{
public:
    struct Sentinel
    {
    };

    class iterator
    {
    public:
        using value_type = std::pair<uint8_t, unsigned char>;
        using difference_type = std::ptrdiff_t;
        using iterator_category = std::input_iterator_tag;
        using pointer = void;
        using reference = value_type;

        iterator(uint16_t mask)
            : index_(0)
            , mask_(mask)
        {
        }

        value_type operator*() const
        {
            return {index_, __builtin_ctzl(mask_)};
        }

        iterator &operator++()
        {
            mask_ &= mask_ - 1;
            ++index_;
            return *this;
        }

        bool operator!=(Sentinel const &) const
        {
            return mask_ != 0;
        }

    private:
        uint8_t index_;
        uint16_t mask_;
    };

    explicit NodeChildrenRange(uint16_t mask)
        : mask_(mask)
    {
    }

    iterator begin() const
    {
        return iterator(mask_);
    }

    Sentinel end() const
    {
        return Sentinel();
    }

private:
    uint16_t mask_;
};

MONAD_MPT_NAMESPACE_END
