#pragma once

#include <category/async/util.hpp>

#include <category/async/detail/start_lifetime_as_polyfill.hpp>

#include <atomic>
#include <filesystem>
#include <mutex>
#include <span>
#include <variant>
#include <vector>

MONAD_ASYNC_NAMESPACE_BEGIN

/* \brief Makes available the lowest possible latency zoned storage, if `zonefs`
is available. Otherwise falls back to an emulation which can use a file on a
filesystem, or a block device.

\todo Actually implement `zonefs` support.

Linux `zonefs` when mounted exposes the NVMe zone namespaces as a POSIX
directory hierarchy. There are two directories in the root:

1. `cnv`, whose contents are all the conventional zones configured on the
storage device. Conventional zones can be read-write modified at will. These
have the block device emulation layer implemented by the storage device, and
thus reads from them have conventional SSD latencies e.g. 70 microseconds.

2. `seq`, whose contents are all the append-only zones configured on the storage
device. Sequential write zones can only be appended to for writes, and once
appended to, nothing already written can be modified. Read from these zones
bypass the block device emulation layer, and thus latencies are very
significantly improved e.g. 15-30 microseconds. Sequential write zones can be
recycled on request, all their contents are disposed of in a single operation
(this corresponds to NAND flash block erase), after which they can be
sequentially written into again.

You can read more about Linux `zonefs` at
https://docs.kernel.org/filesystems/zonefs.html.

This class is a thin wrapper around Linux `zonefs` if it is fed filesystem
paths to `zonefs` mounts. If it is fed a raw partition or a file on a
filesystem, it chops up that space into 256Mb chunks and exposes those as a
single conventional zone, and the remainder as sequential write zones. The
semantics are correctly emulated: resetting a chunk sends through a TRIM command
to the underlying storage, this will cause filesystems to truly deallocate
storage and raw partitions to issue a TRIM command to their hardware. This in
turn prevents garbage collection i/o storms caused by SSDs initiating forced
background TRIM during normal i/o to free up blocks, which introduces
pathological i/o performance loss at usually the most inconvenient times.
*/
class storage_pool
{
public:
    //! \brief Type of chunk, conventional or sequential
    enum chunk_type
    {
        cnv = 0,
        seq = 1
    };

    /*! \brief A source of backing storage for the storage pool.
     */
    class device
    {
        friend class storage_pool;

        int const cached_readwritefd_; // used for the device memory map of its
                                       // metadata (not O_DIRECT)
        int uncached_readfd_; // may or may not be shared by chunks for random
                              // read i/o (O_DIRECT)
        int uncached_writefd_; // may or may not be shared by chunks
                               // for append i/o (O_DIRECT)
        const enum class type_t_ : uint8_t {
            unknown,
            file,
            block_device,
            zoned_device
        } type_;
        uint64_t const unique_hash_;
        file_offset_t const size_of_file_;

        struct metadata_t
        {
            // Preceding this is an array of uint32_t of chunk bytes used

            uint32_t spare_[13]; // set aside for flags later
            uint32_t config_hash; // hash of this configuration
            uint32_t chunk_capacity;
            uint8_t magic[4]; // "MND0" for v1 of this metadata

            size_t chunks(file_offset_t end_of_this_offset) const noexcept
            {
                end_of_this_offset -= sizeof(metadata_t);
                auto ret =
                    end_of_this_offset / (chunk_capacity + sizeof(uint32_t));
                // We need the front CPU_PAGE_SIZE of this metadata to not
                // include any chunk
                auto endofchunks =
                    round_down_align<CPU_PAGE_BITS>(ret * chunk_capacity);
                auto startofmetadata = round_down_align<CPU_PAGE_BITS>(
                    end_of_this_offset - ret * sizeof(uint32_t));
                if (startofmetadata == endofchunks) {
                    return ret - 1;
                }
                return ret;
            }

            // Only used for seq chunks
            std::span<std::atomic<uint32_t>>
            chunk_bytes_used(file_offset_t end_of_this_offset) const noexcept
            {
                static_assert(
                    sizeof(uint32_t) == sizeof(std::atomic<uint32_t>));
                auto count = chunks(end_of_this_offset);
                return {
                    start_lifetime_as_array<std::atomic<uint32_t>>(
                        const_cast<std::byte *>(
                            reinterpret_cast<std::byte const *>(this)) -
                            count * sizeof(uint32_t),
                        count),
                    count};
            }

            // Bytes used by the pool metadata on this device
            size_t total_size(file_offset_t end_of_this_offset) const noexcept
            {
                auto count = chunks(end_of_this_offset);
                return sizeof(metadata_t) + count * sizeof(uint32_t);
            }
        } *const metadata_;

        static_assert(sizeof(metadata_t) == 64);

        constexpr device(
            int cached_readwritefd, type_t_ type, uint64_t unique_hash,
            file_offset_t size_of_file, metadata_t *metadata)
            : cached_readwritefd_(cached_readwritefd)
            , uncached_readfd_(-1)
            , uncached_writefd_(-1)
            , type_(type)
            , unique_hash_(unique_hash)
            , size_of_file_(size_of_file)
            , metadata_(metadata)
        {
        }

    public:
        //! The current filesystem path of the device (it can change over time)
        std::filesystem::path current_path() const;

        //! Returns if this device is a file on a filesystem
        bool is_file() const noexcept
        {
            return type_ == type_t_::file;
        }

        //! Returns if this device is a block device e.g. a raw partition
        bool is_block_device() const noexcept
        {
            return type_ == type_t_::block_device;
        }

        //! Returns if this device is a zonefs mount
        bool is_zoned_device() const noexcept
        {
            return type_ == type_t_::zoned_device;
        }

        //! Returns the number of chunks on this device
        size_t chunks() const;
        //! Returns the capacity of the device, and how much of that is
        //! currently filled with data, in that order.
        std::pair<file_offset_t, file_offset_t> capacity() const;
    };

    /*! \brief A zone chunk from storage, which is always managed by a shared
    ptr. When the shared ptr count reaches zero, any file descriptors or other
    resources associated with the chunk are released.
     */
    class chunk
    {
        friend class storage_pool;

    protected:
        class device &device_;
        int read_fd_{-1}, write_fd_{-1};
        file_offset_t const offset_{file_offset_t(-1)},
            capacity_{file_offset_t(-1)};
        uint32_t const chunkid_within_device_{uint32_t(-1)};
        uint32_t const chunkid_within_zone_{uint32_t(-1)};
        bool const owns_readfd_{false}, owns_writefd_{false},
            append_only_{false};

        constexpr chunk(
            class device &device, int read_fd, int write_fd,
            file_offset_t offset, file_offset_t capacity,
            uint32_t chunkid_within_device, uint32_t chunkid_within_zone,
            bool owns_readfd, bool owns_writefd, bool append_only)
            : device_(device)
            , read_fd_(read_fd)
            , write_fd_(write_fd)
            , offset_(offset)
            , capacity_(capacity)
            , chunkid_within_device_(chunkid_within_device)
            , chunkid_within_zone_(chunkid_within_zone)
            , owns_readfd_(owns_readfd)
            , owns_writefd_(owns_writefd)
            , append_only_(append_only)
        {
        }

    public:
        chunk(chunk const &) = delete;
        chunk(chunk &&) = delete;
        virtual ~chunk();

        //! \brief Returns the storage device this chunk is stored upon
        class device &device() noexcept
        {
            return device_;
        }

        //! \brief Returns the storage device this chunk is stored upon
        const class device &device() const noexcept
        {
            return device_;
        }

        //! \brief Returns whether this chunk is a conventional write chunk
        bool is_conventional_write() const noexcept
        {
            return !append_only_;
        }

        //! \brief Returns whether this chunk is a sequential write chunk
        bool is_sequential_write() const noexcept
        {
            return append_only_;
        }

        //! \brief Returns a file descriptor able to read from the chunk, along
        //! with any offset which needs to be added to any i/o performed with it
        std::pair<int, file_offset_t> read_fd() const noexcept
        {
            return {read_fd_, offset_};
        }

        //! \brief Returns a file descriptor able to write to the chunk, along
        //! with any offset which needs to be added to any i/o performed with it
        std::pair<int, file_offset_t>
        write_fd(size_t bytes_which_shall_be_written) noexcept;

        //! \brief Returns the capacity of the zone
        file_offset_t capacity() const noexcept
        {
            return capacity_;
        }

        //! \brief Returns the type of zone and id within that zone (starts from
        //! zero for conventional and sequential)
        std::pair<chunk_type, uint32_t> zone_id() const noexcept
        {
            if (append_only_) {
                return {chunk_type::seq, chunkid_within_zone_};
            }
            return {chunk_type::cnv, chunkid_within_zone_};
        }

        //! \brief Returns the current amount of the zone filled with data (note
        //! the OS syscall can sometimes lag reality for a few milliseconds)
        file_offset_t size() const;

        //! \brief Destroys the contents of the chunk, releasing the backing
        //! storage for use by others.
        void destroy_contents();

        //! \brief Clones part or all of the contents of the chunk into another
        //! chunk, using kernel offload where available. The destination chunk
        //! MUST be empty if it is sequential append only, otherwise the call
        //! fails.
        uint32_t clone_contents_into(chunk &other, uint32_t bytes);

        /*! \brief Tries to trim the contents of a chunk by efficiently
        discarding the tail of the contents. If not possible to do efficiently,
        return false.
        */
        bool try_trim_contents(uint32_t bytes);
    };

    /*! \brief A conventional zone chunk from the `cnv` subdirectory.
     */
    class cnv_chunk final : public chunk
    {
        friend class storage_pool;

        using chunk::chunk;

    public:
        bool is_conventional_write() const noexcept
        {
            return true;
        }

        bool is_sequential_write() const noexcept
        {
            return false;
        }
    };

    /*! \brief An append-only sequential write zone chunk from the `seq`
     * subdirectory.
     */
    class seq_chunk final : public chunk
    {
        friend class storage_pool;

        using chunk::chunk;

    public:
        bool is_conventional_write() const noexcept
        {
            return false;
        }

        bool is_sequential_write() const noexcept
        {
            return true;
        }
    };

    //! \brief What to do when opening the pool for use.
    enum class mode
    {
        open_existing,
        create_if_needed,
        truncate
    };

    //! \brief Flags for storage pool creation
    struct creation_flags
    {
        //! How much to shift left a bit to set chunk capacity during creation.
        //! The maximum is 32 (4Gb).
        uint32_t chunk_capacity : 5;
        //! Whether to interleave chunks evenly during creation
        uint32_t interleave_chunks_evenly : 1;
        //! Whether to open the database read-only
        uint32_t open_read_only : 1;
        //! Whether to open the database read-only allowing a dirty closed
        //! database
        uint32_t open_read_only_allow_dirty : 1;
        //! Whether to disable the check which prevents use of a storage config
        //! different to the one the pool was created with. Disabling that check
        //! can cause pool data loss, as well as system data loss as it will
        //! happily use any partition you feed it, including the system drive.
        uint32_t disable_mismatching_storage_pool_check : 1;

        constexpr creation_flags()
            : chunk_capacity(28)
            , interleave_chunks_evenly(false)
            , open_read_only(false)
            , open_read_only_allow_dirty(false)
            , disable_mismatching_storage_pool_check(false)
        {
        }
    };

    using chunk_ptr = std::shared_ptr<class chunk>;
    using cnv_chunk_ptr = std::shared_ptr<cnv_chunk>;
    using seq_chunk_ptr = std::shared_ptr<seq_chunk>;

private:
    bool const is_read_only_, is_read_only_allow_dirty_, is_newly_truncated_;
    std::vector<device> devices_;

    // Lock protects everything below this
    mutable std::mutex lock_;

    struct chunk_info_
    {
        std::weak_ptr<class chunk> chunk;
        class device &device;
        uint32_t const chunk_offset_into_device;
    };

    std::vector<chunk_info_> chunks_[2];

    device make_device_(
        mode op, device::type_t_ type, std::filesystem::path const &path,
        int fd, std::variant<uint64_t, device const *> dev_no_or_dev,
        creation_flags flags);

    void fill_chunks_(creation_flags const &flags);

    struct clone_as_read_only_tag_
    {
    };

    storage_pool(storage_pool const *src, clone_as_read_only_tag_);

public:
    //! \brief Constructs a storage pool from the list of backing storage
    //! sources
    explicit storage_pool(
        std::span<std::filesystem::path const> sources,
        mode mode = mode::create_if_needed, creation_flags flags = {});

    //! \brief Constructs a storage pool from a temporary anonymous inode.
    //! Useful for test code.
    explicit storage_pool(use_anonymous_inode_tag, creation_flags flags = {});
    ~storage_pool();

    //! \brief True if the storage pool was opened read only
    bool is_read_only() const noexcept
    {
        return is_read_only_;
    }

    //! \brief True if the storage pool was opened read only but a dirty closed
    //! state is to be allowed
    bool is_read_only_allow_dirty() const noexcept
    {
        return is_read_only_allow_dirty_;
    }

    //! \brief True if the storage pool was just truncated, and structures may
    //! need reinitialising
    bool is_newly_truncated() const noexcept
    {
        return is_newly_truncated_;
    }

    //! \brief Returns a list of the backing storage devices
    std::span<device const> devices() const noexcept
    {
        return {devices_};
    }

    //! \brief Returns the number of chunks for the specified type
    size_t chunks(chunk_type which) const noexcept
    {
        return chunks_[which].size();
    }

    //! \brief Returns the number of currently active chunks for the specified
    //! type
    size_t currently_active_chunks(chunk_type which) const noexcept;
    //! \brief Get an existing chunk, if it is activated
    std::shared_ptr<class chunk> chunk(chunk_type which, uint32_t id) const;
    //! \brief Activate a chunk (i.e. open file descriptors to it, if necessary)
    std::shared_ptr<class chunk> activate_chunk(chunk_type which, uint32_t id);

    //! \brief Clones an existing storage pool as read-only
    storage_pool clone_as_read_only() const;
};

MONAD_ASYNC_NAMESPACE_END
