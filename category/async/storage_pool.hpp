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

#pragma once

#include <category/async/util.hpp>
#include <category/core/assert.h>

#include <category/core/detail/start_lifetime_as_polyfill.hpp>

#include <atomic>
#include <filesystem>
#include <type_traits>
#include <variant>

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
    class device_t
    {
        friend class storage_pool;

        int const readwritefd_; // shared by all chunks for cached i/o
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

            uint32_t spare_[12]; // set aside for flags later
            uint32_t num_cnv_chunks; // conventional chunks ahead of the rest
            uint32_t config_hash; // hash of this configuration
            uint32_t chunk_capacity;
            uint8_t magic[4]; // "MND0" for v1 of this metadata

            size_t chunks(file_offset_t end_of_this_offset) const noexcept
            {
                end_of_this_offset -= sizeof(metadata_t);
                auto const ret =
                    end_of_this_offset / (chunk_capacity + sizeof(uint32_t));
                // We need the front CPU_PAGE_SIZE of this metadata to not
                // include any chunk
                auto const endofchunks =
                    round_down_align<CPU_PAGE_BITS>(ret * chunk_capacity);
                auto const startofmetadata = round_down_align<CPU_PAGE_BITS>(
                    end_of_this_offset - ret * sizeof(uint32_t));
                if (startofmetadata == endofchunks) {
                    return ret - 1;
                }
                return ret;
            }

            // Only used for seq chunks. Returns an atomic view of the
            // per-chunk bytes-used counter at `index`; the underlying uint32_t
            // aliases shared on-disk storage, so access is always atomic.
            std::atomic_ref<uint32_t> chunk_bytes_used_at(
                file_offset_t const end_of_this_offset,
                size_t const index) const noexcept
            {
                static_assert(
                    sizeof(uint32_t) == sizeof(std::atomic<uint32_t>));
                auto const count = chunks(end_of_this_offset);
                auto *const base = start_lifetime_as_array<uint32_t>(
                    const_cast<std::byte *>(
                        reinterpret_cast<std::byte const *>(this)) -
                        count * sizeof(uint32_t),
                    count);
                return std::atomic_ref<uint32_t>(base[index]);
            }

            // Bytes used by the pool metadata on this device
            size_t
            total_size(file_offset_t const end_of_this_offset) const noexcept
            {
                auto const count = chunks(end_of_this_offset);
                return sizeof(metadata_t) + count * sizeof(uint32_t);
            }
        } *const metadata_;

        static_assert(sizeof(metadata_t) == 64);

        constexpr device_t(
            int const readwritefd, type_t_ const type,
            uint64_t const unique_hash, file_offset_t const size_of_file,
            metadata_t *const metadata)
            : readwritefd_(readwritefd)
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

        //! Returns the number of cnv chunks on this device
        size_t cnv_chunks() const;
        //! Returns the capacity of the device, and how much of that is
        //! currently filled with data, in that order.
        std::pair<file_offset_t, file_offset_t> capacity() const;
    };

    /*! \brief A chunk of storage, derived from its id and cheap to copy. It
    borrows the pool's device -- including the descriptor every chunk reads
    and writes through -- so it must not outlive the pool.
     */
    class chunk_t
    {
        friend class storage_pool;

        device_t &device_;
        file_offset_t const offset_{file_offset_t(-1)},
            capacity_{file_offset_t(-1)};
        uint32_t const chunkid_within_device_{uint32_t(-1)};
        uint32_t const chunkid_within_zone_{uint32_t(-1)};
        bool const append_only_{false};

    public:
        constexpr chunk_t(
            device_t &device, file_offset_t const offset,
            file_offset_t const capacity, uint32_t const chunkid_within_device,
            uint32_t const chunkid_within_zone, bool const append_only)
            : device_(device)
            , offset_(offset)
            , capacity_(capacity)
            , chunkid_within_device_(chunkid_within_device)
            , chunkid_within_zone_(chunkid_within_zone)
            , append_only_(append_only)
        {
        }

        //! \brief Returns the storage device this chunk is stored upon
        device_t &device() noexcept
        {
            return device_;
        }

        //! \brief Returns the storage device this chunk is stored upon
        device_t const &device() const noexcept
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
            return {device_.readwritefd_, offset_};
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
        uint32_t clone_contents_into(chunk_t &other, uint32_t bytes);

        /*! \brief Tries to trim the contents of a chunk by efficiently
        discarding the tail of the contents. If not possible to do efficiently,
        return false.
        */
        bool try_trim_contents(uint32_t bytes);
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
        static constexpr uint32_t MAX_CHUNK_CAPACITY_BITS = (1 << 5) - 1;

        //! How much to shift left a bit to set chunk capacity during creation.
        //! The maximum is 32 (4Gb).
        uint32_t chunk_capacity : 5;
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
        //! Whether to permit on-disk format migration on open. Default false;
        //! only monad-mpt --upgrade sets this to true. When false, a
        //! DbMetadataContext ctor that observes PREVIOUS_MAGIC aborts with a
        //! message directing the operator to run monad-mpt --upgrade.
        uint32_t allow_migration : 1;

        //! Number of conventional chunks to allocate. Default is 3.
        uint32_t num_cnv_chunks;

        constexpr creation_flags()
            : chunk_capacity(28)
            , open_read_only(false)
            , open_read_only_allow_dirty(false)
            , disable_mismatching_storage_pool_check(false)
            , allow_migration(false)
            , num_cnv_chunks(3)
        {
        }

        //! Set chunk_capacity with range validation; direct assignment to
        //! the 5-bit field would silently truncate an oversized value.
        constexpr void set_chunk_capacity(uint32_t const bits)
        {
            MONAD_ASSERT(bits <= MAX_CHUNK_CAPACITY_BITS);
            chunk_capacity = bits & MAX_CHUNK_CAPACITY_BITS;
        }
    };

private:
    bool const is_read_only_, is_read_only_allow_dirty_, is_migration_allowed_,
        is_newly_truncated_;
    device_t device_;
    // A chunk's whole geometry follows from its id, so these counts are all
    // the pool keeps per chunk type.
    uint32_t cnv_chunks_count_{0}, seq_chunks_count_{0};

    static device_t make_device_(
        mode op, device_t::type_t_ type, std::filesystem::path const &path,
        int fd, std::variant<uint64_t, device_t const *> dev_no_or_dev,
        creation_flags flags);

    // device_ has const members and so must be built before the constructor
    // body runs; each of these opens one source into a ready device_t.
    static device_t open_device_(
        std::filesystem::path const &source, mode op, creation_flags flags);
    static device_t reopen_device_read_only_(device_t const &src);
    static device_t make_anonymous_device_(off_t len, creation_flags flags);

    // Stamps the config hash on a blank device, aborts if an existing one
    // disagrees, and establishes the chunk counts.
    void adopt_device_(creation_flags const &flags);

    struct clone_as_read_only_tag_
    {
    };

    storage_pool(storage_pool const *src, clone_as_read_only_tag_);

public:
    //! \brief Constructs a storage pool from its backing storage source
    explicit storage_pool(
        std::filesystem::path const &source, mode mode = mode::create_if_needed,
        creation_flags flags = {});

    //! \brief Constructs a storage pool from a temporary anonymous inode.
    //! Useful for test code.
    explicit storage_pool(use_anonymous_inode_tag, creation_flags flags = {});

    //! \brief Constructs a storage pool from a temporary anonymous inode with a
    //! specific size. Useful for test code.
    explicit storage_pool(
        use_anonymous_sized_inode_tag, off_t len, creation_flags flags = {});

    // Copying would double-close the device descriptor and double-unmap its
    // metadata.
    storage_pool(storage_pool const &) = delete;
    storage_pool &operator=(storage_pool const &) = delete;

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

    //! \brief True if the storage pool was opened with allow_migration set.
    //! Consulted by DbMetadataContext to decide whether a PREVIOUS_MAGIC
    //! pool should be migrated or rejected with a "run monad-mpt --upgrade"
    //! message.
    bool is_migration_allowed() const noexcept
    {
        return is_migration_allowed_;
    }

    //! \brief True if the storage pool was just truncated, and structures may
    //! need reinitialising
    bool is_newly_truncated() const noexcept
    {
        return is_newly_truncated_;
    }

    //! \brief Returns the backing storage device
    device_t const &device() const noexcept
    {
        return device_;
    }

    //! \brief Returns the number of chunks for the specified type
    size_t chunks(chunk_type const which) const noexcept
    {
        return which == cnv ? cnv_chunks_count_ : seq_chunks_count_;
    }

    //! \brief The chunk of this type with this id, by value. It borrows the
    //! pool's device, so it must not outlive the pool.
    chunk_t chunk(chunk_type which, uint32_t id);

    //! \brief Clones an existing storage pool as read-only
    storage_pool clone_as_read_only() const;
};

// chunk() builds one of these per i/o, so nothing may need running when one
// goes away.
static_assert(std::is_trivially_destructible_v<storage_pool::chunk_t>);

MONAD_ASYNC_NAMESPACE_END
