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
#include <mutex>
#include <optional>
#include <span>
#include <variant>
#include <vector>

MONAD_ASYNC_NAMESPACE_BEGIN

namespace test
{
    struct StoragePoolTestAccess; // test-only access to the hash formulae
}

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
    friend struct test::StoragePoolTestAccess;

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
            uint32_t num_cnv_chunks; // number of cnv chunks per device
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

        // True if this open wrote the device's footer, i.e. it was blank
        // beforehand.
        bool const is_freshly_initialised_;

        static_assert(sizeof(metadata_t) == 64);

        // Base address and length of the mapping make_device_ established over
        // this device's metadata. The base is CPU page aligned.
        std::pair<void *, size_t> metadata_mapping_() const noexcept;

        // Writes back this device's footer and per-chunk bytes-used array,
        // returning once the storage reports them durable.
        void flush_metadata_() const;

        constexpr device_t(
            int const readwritefd, type_t_ const type,
            uint64_t const unique_hash, file_offset_t const size_of_file,
            metadata_t *const metadata, bool const is_freshly_initialised)
            : readwritefd_(readwritefd)
            , type_(type)
            , unique_hash_(unique_hash)
            , size_of_file_(size_of_file)
            , metadata_(metadata)
            , is_freshly_initialised_(is_freshly_initialised)
        {
        }

    public:
        //! Returns whether this open wrote the device's footer, i.e. whether
        //! the device was blank before this pool was constructed
        bool is_freshly_initialised() const noexcept
        {
            return is_freshly_initialised_;
        }

        //! The size of the device in bytes, as of when this pool opened it.
        //! This is the quantity chunks() and the device's unique_hash are
        //! derived from, so it is what has to be recorded to later recover
        //! the geometry of a device grown in place.
        file_offset_t size_bytes() const noexcept
        {
            return size_of_file_;
        }

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

    /*! \brief A zone chunk from storage, which is always managed by a shared
    ptr. When the shared ptr count reaches zero, any file descriptors or other
    resources associated with the chunk are released.
     */
    class chunk_t
    {
        friend class storage_pool;

        device_t &device_;
        int read_fd_{-1}, write_fd_{-1};
        file_offset_t const offset_{file_offset_t(-1)},
            capacity_{file_offset_t(-1)};
        uint32_t const chunkid_within_device_{uint32_t(-1)};
        uint32_t const chunkid_within_zone_{uint32_t(-1)};
        bool const owns_readfd_{false}, owns_writefd_{false},
            append_only_{false};

    public:
        constexpr chunk_t(
            device_t &device, int const read_fd, int const write_fd,
            file_offset_t const offset, file_offset_t const capacity,
            uint32_t const chunkid_within_device,
            uint32_t const chunkid_within_zone, bool const owns_readfd,
            bool const owns_writefd, bool const append_only)
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

        virtual ~chunk_t();

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
        //! Every source must already carry pool metadata; abort if one does
        //! not.
        open_existing,
        //! Initialise any source which does not, and open the rest as they are.
        create_if_needed,
        //! Discard every source's contents and initialise all of them.
        truncate,
        //! Take up storage the sources now offer but the pool does not yet
        //! use: initialise and join a blank suffix, and relocate the metadata
        //! of a last device extended in place. Existing data is kept, and
        //! re-running the same list resumes an interrupted run.
        add_devices
    };

    //! \brief How much space a database's metadata needs in the first half of
    //! conventional chunk 0, supplied by the caller that owns that layout so
    //! this layer needs no knowledge of it.
    struct db_metadata_budget
    {
        //! Fixed header, ahead of the per-chunk array. Should be the largest
        //! of any on-disk format the caller can still read, so a pool stays
        //! migratable without remapping.
        size_t header_bytes;
        //! Cost of each sequential chunk in the per-chunk array.
        size_t bytes_per_chunk;
    };

    //! Smallest chunk capacity any pool carrying a database can have been
    //! created with. This layer enforces no minimum of its own; the floor
    //! comes from the database metadata having to fit in half of conventional
    //! chunk 0, which the owning layer enforces on open. Every chunk therefore
    //! starts at a multiple of this, and it is a power of two, which makes it a
    //! safe stride for sampling chunk starts on a device whose own geometry is
    //! not known yet.
    static constexpr uint32_t min_chunk_capacity = 1u << 21;

    //! \brief Flags for storage pool creation
    struct creation_flags
    {
        static constexpr uint32_t MAX_CHUNK_CAPACITY_BITS = (1 << 5) - 1;

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
        //! Whether to permit on-disk format migration on open. Default false;
        //! only monad-mpt --upgrade sets this to true. When false, a
        //! DbMetadataContext ctor that observes PREVIOUS_MAGIC aborts with a
        //! message directing the operator to run monad-mpt --upgrade.
        uint32_t allow_migration : 1;

        //! Number of conventional chunks to allocate per device. Default is 3.
        uint32_t num_cnv_chunks;

        //! What db_metadata recorded as the size of the device which grew:
        //! its size before the extend. Only one device can have grown, the
        //! last the pool already owns, so this needs no device index.
        std::optional<file_offset_t> recorded_size_of_grown_device;

        //! Space the database's metadata needs, from the caller that owns that
        //! layout. Nothing if there is no database.
        std::optional<db_metadata_budget> metadata_budget;

        constexpr creation_flags()
            : chunk_capacity(28)
            , interleave_chunks_evenly(false)
            , open_read_only(false)
            , open_read_only_allow_dirty(false)
            , disable_mismatching_storage_pool_check(false)
            , allow_migration(false)
            , num_cnv_chunks(3)
            , recorded_size_of_grown_device(std::nullopt)
            , metadata_budget(std::nullopt)
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
        is_newly_truncated_, is_adding_devices_;
    std::vector<device_t> devices_;

    // Lock protects everything below this
    mutable std::mutex lock_;

    std::vector<chunk_t> chunks_[2];

    // The pool metadata a device carries in its final sizeof(metadata_t)
    // bytes, as read back. Absent on a blank device, and on one extended in
    // place, which strands the footer mid-device.
    struct device_pool_metadata_
    {
        uint32_t chunk_capacity;
        uint32_t num_cnv_chunks;
        uint32_t config_hash;
        size_t chunks;
    };

    // How the filesystem identifies the path a device was read from. Used to
    // reject a source listed twice, which unique_hash cannot do: block devices
    // fold a constant dev_no, so two distinct same-sized ones collide by
    // construction.
    struct device_identity_
    {
        uint64_t dev;
        uint64_t ino;
        // Target device number for a block device special file, so that two
        // distinct special files naming the same device also compare equal;
        // 0 (never a valid rdev) otherwise.
        uint64_t rdev;
        // The device number compute_unique_hash_ was given, so that the hash
        // can be recomputed at a different size -- which is what validating a
        // grown device's previous size needs.
        uint64_t hash_dev_no;
    };

    // Read-only description of a candidate source, gathered before anything is
    // written. Everything mode::add_devices validates is derivable from this,
    // so a rejected device set is never modified. unique_hash is stored
    // already-computed rather than as its inputs, so this can equally describe
    // a live device_t, which keeps only the finished hash.
    struct device_info_
    {
        device_t::type_t_ type;
        uint64_t unique_hash;
        // Current size: BLKGETSIZE64 for a block device, st_size for a file.
        file_offset_t size;
        std::optional<device_pool_metadata_> pool_metadata;
        // Absent when this describes a live device_t, which keeps no record of
        // the path it was opened from.
        std::optional<device_identity_> identity;
        // BLKSSZGET for a block device, in bytes. Nothing for a file, or if
        // the ioctl fails.
        std::optional<uint32_t> logical_block_size;
    };

    // Everything about `source` that needs no read of its contents. `fd` must
    // be open on it.
    static device_info_
    read_device_identity_(int fd, std::filesystem::path const &source);

    // The above, plus the pool metadata read back from the device's end.
    static device_info_ read_device_info_(std::filesystem::path const &source);

    // Both must carry an identity, so both must have come from a path.
    static bool
    same_device_identity_(device_info_ const &a, device_info_ const &b);

    // Aborts if two sources name the same underlying device, which would
    // otherwise alias the same storage under two chunk id ranges. A pass of
    // its own ahead of every mode, because make_device_ initialises as it
    // goes: by the time the duplicate is reached, the first copy has been
    // written to.
    static void
    refuse_duplicate_sources_(std::span<std::filesystem::path const> sources);

    // The per-device and whole-pool hash formulae, each in one place so the
    // validating pre-pass and fill_chunks_ cannot drift apart. Members rather
    // than file-local statics because device_t::type_t_ is private to device_t
    // and only storage_pool is its friend.
    static uint64_t compute_unique_hash_(
        device_t::type_t_ type, uint64_t dev_no, file_offset_t size);

    static uint32_t compute_config_hash_(std::span<device_info_ const>);

    static device_info_ device_info_of_(device_t const &);

    // A source which grew in place: it presents no footer at the end its
    // current size gives it, because extending strands the footer mid-device,
    // but carries a stranded one below which validates against the pool's own
    // hash.
    struct grown_device_
    {
        size_t index; // position within the source list
        // The recorded size, once validated: the size this device had when it
        // was last part of this pool, exact to the byte.
        file_offset_t previous_size;
        size_t previous_chunks; // chunks() at previous_size
        uint32_t chunk_capacity; // read back from the stranded footer
        uint32_t num_cnv_chunks;
    };

    // What a validated mode::add_devices open is going to do. Everything here
    // is decided before a byte is written, so a refused device set is left
    // untouched.
    struct add_devices_plan_
    {
        // Sources [0, members) already carry a footer at their end. Sources
        // from members on are initialised and joined, except for a grown one,
        // which sits at index `members` and keeps its contents.
        size_t members;
        std::optional<grown_device_> grown;
        // config_hash of the set this operation produces.
        uint32_t target_hash;
        // Geometry every joining device is carved at. Taken from device 0's
        // footer, or from the grown device's stranded footer when device 0
        // is itself the one that grew.
        uint32_t chunk_capacity;
        uint32_t num_cnv_chunks;
    };

    // Validates the mode::add_devices preconditions and returns the plan.
    // Aborts, having written nothing, if the joining devices are not a
    // contiguous suffix, if a joining device is not verifiably blank, if a
    // source other than the last the pool owns grew, if a source grew but
    // `recorded_size` does not describe the pool it grew out of, if a
    // pre-existing source hashes to none of the sets this operation can
    // legitimately see, or if the result would exceed the chunk id space or
    // `budget`.
    static add_devices_plan_ validate_devices_to_add_(
        std::span<std::filesystem::path const> sources,
        std::span<device_info_ const> infos,
        std::optional<file_offset_t> recorded_size,
        std::optional<db_metadata_budget> const &budget);

    // Reads the sizeof(metadata_t) bytes a footer would occupy if the device
    // were exactly `size` bytes long, and returns it if it carries the magic.
    static std::optional<device_t::metadata_t>
    read_footer_for_size_(int fd, file_offset_t size);

    // The device as it was before it grew, which is what the pool's pre-grow
    // config_hash covers.
    static device_info_ device_info_at_previous_size_(
        device_info_ const &now, grown_device_ const &grown);

    // Checks `recorded_size` against the footer stranded there by the extend
    // which grew `source`, for a source presenting no footer at its end.
    // `members` are the sources ahead of it, all of which do carry one.
    // Returns nothing unless that footer describes the pool as it was at
    // `recorded_size`; `footer_found` then distinguishes a size with no footer
    // at all from one whose footer belongs elsewhere. Reads only.
    static std::optional<grown_device_> validate_grown_device_(
        std::filesystem::path const &source, device_info_ const &current,
        std::span<device_info_ const> members,
        std::optional<file_offset_t> recorded_size, bool &footer_found);

    // Writes the grown device's metadata region at the end its current size
    // gives it: the bytes-used array carried over from the region stranded at
    // `grown.previous_size` with the new chunks zeroed, then the footer. The
    // footer is written and made durable last, so it is the commit record.
    static void relocate_device_metadata_(
        std::filesystem::path const &source, file_offset_t current_size,
        grown_device_ const &grown, uint32_t new_config_hash);

    // Rewrites the config_hash of the footer already at the end of `source`.
    static void stamp_config_hash_(
        std::filesystem::path const &source, file_offset_t size, uint32_t hash);

    device_t make_device_(
        mode op, device_t::type_t_ type, std::filesystem::path const &path,
        int fd, std::variant<uint64_t, device_t const *> dev_no_or_dev,
        creation_flags flags);

    void fill_chunks_(mode op, creation_flags const &flags);

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

    //! \brief Constructs a storage pool from a temporary anonymous inode with a
    //! specific size. Useful for test code.
    explicit storage_pool(
        use_anonymous_sized_inode_tag, off_t len, creation_flags flags = {});

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

    //! \brief True if the storage pool was opened with mode::add_devices.
    //! Consulted by DbMetadataContext to decide whether a pool reporting more
    //! chunks than the metadata describes should be grown or rejected with a
    //! "run monad-mpt --rescan-devices" message.
    bool is_adding_devices() const noexcept
    {
        return is_adding_devices_;
    }

    //! \brief Returns a list of the backing storage devices
    std::span<device_t const> devices() const noexcept
    {
        return {devices_};
    }

    //! \brief Returns whether `source` already carries storage pool metadata.
    //! Read-only. Lets tooling tell a device already belonging to a pool from
    //! a blank one before attempting a mode::add_devices open.
    static bool has_pool_metadata(std::filesystem::path const &source);

    //! \brief What a mode::add_devices open of `sources` would do, decided
    //! without writing anything.
    struct rescan_preview
    {
        //! Leading sources which already carry a footer at their end.
        size_t existing;
        //! The validated previous size of the source at index `existing`: the
        //! size it had before it was extended in place, zero if none was. A
        //! source which grew keeps its contents.
        file_offset_t grown_previous_size;
        //! Total chunks, cnv and seq, that source offered at its previous
        //! size.
        size_t grown_previous_chunks;
        //! First source which will be initialised, destroying whatever is on
        //! it. Equal to sources.size() when there is none.
        size_t first_initialised;
    };

    //! \brief Classifies `sources` as a mode::add_devices open would, writing
    //! nothing. It applies the same refusals, so a caller can put an accurate
    //! confirmation prompt in front of the operation and know the operation
    //! will not then refuse it. `recorded_size` is what db_metadata holds for
    //! the source which grew; the validated previous size it yields comes back
    //! in `grown_previous_size`.
    static rescan_preview preview_rescan(
        std::span<std::filesystem::path const> sources,
        std::optional<file_offset_t> recorded_size = std::nullopt,
        std::optional<db_metadata_budget> const &budget = std::nullopt);

    //! \brief Returns the number of chunks for the specified type
    size_t chunks(chunk_type const which) const noexcept
    {
        return chunks_[which].size();
    }

    //! \brief Get an existing chunk, if it is activated
    chunk_t &chunk(chunk_type which, uint32_t id);

    //! \brief Clones an existing storage pool as read-only
    storage_pool clone_as_read_only() const;

private:
    //! \brief Activate a chunk (i.e. open file descriptors to it, if necessary)
    chunk_t activate_chunk(
        chunk_type which, device_t &device, uint32_t id_within_device,
        uint32_t id_within_zone);
};

MONAD_ASYNC_NAMESPACE_END
