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

/**
 * @file
 *
 * This files defines a unified interface for working with event ring files.
 * event capture files, and block capture files
 */

#include <cstdint>
#include <filesystem>
#include <optional>
#include <string>
#include <utility>

#include <category/core/event/evcap_reader.h>
#include <category/core/event/event_def.h>
#include <category/core/event/event_ring.h>

struct monad_bcap_archive;

struct EventIterator;
struct EventSourceQuery;

enum class EventRingLiveness
{
    Unknown,
    Live,
    Abandoned,
    Snapshot,
};

constexpr char const *describe(EventRingLiveness l)
{
    using enum EventRingLiveness;
    switch (l) {
    case Live:
        return "live";
    case Abandoned:
        return "abandoned";
    case Snapshot:
        return "snapshot";
    default:
        return "<unknown>";
    }
}

struct EventIterator;
struct EventSourceSpec;

/// Events can come from event ring files, event capture files, or files in a
/// block archive directory; this interface represents the common functionality
/// of all of them
class EventSourceFile
{
public:
    enum class Type : uint8_t
    {
        EventRing,
        EventCaptureFile,
        BlockArchiveDirectory,
    };

    virtual ~EventSourceFile() = default;
    virtual std::string describe() const = 0;

    virtual Type get_type() const = 0;
    virtual std::filesystem::path const &get_origin_path() const = 0;
    virtual int get_file_descriptor() const = 0;
    virtual bool is_finalized() const = 0;
    virtual bool is_interactive() const = 0;
    virtual std::string validate(EventSourceSpec const &) const = 0;
    [[nodiscard]] virtual std::string
    init_iterator(EventIterator *, EventSourceSpec const &) const = 0;
};

class MappedEventRing : public EventSourceFile
{
public:
    MappedEventRing() = delete;
    MappedEventRing(MappedEventRing const &) = delete;
    MappedEventRing(MappedEventRing &&) noexcept;
    ~MappedEventRing() override;

    explicit MappedEventRing(
        std::filesystem::path origin_path, int ring_fd,
        EventRingLiveness initial_liveness, monad_event_ring const &event_ring)
        : origin_path_{std::move(origin_path)}
        , ring_fd_{ring_fd}
        , initial_liveness_{initial_liveness}
        , force_live_{false}
        , event_ring_{event_ring}
    {
    }

    std::string describe() const override;

    std::filesystem::path const &get_origin_path() const override
    {
        return origin_path_;
    }

    int get_file_descriptor() const override
    {
        return ring_fd_;
    }

    Type get_type() const override
    {
        return Type::EventRing;
    }

    bool is_finalized() const override;

    bool is_interactive() const override
    {
        return initial_liveness_ == EventRingLiveness::Live;
    }

    EventRingLiveness get_initial_liveness() const
    {
        return initial_liveness_;
    }

    monad_event_ring const *get_event_ring() const
    {
        return &event_ring_;
    }

    monad_event_ring_header const *get_header() const
    {
        return event_ring_.header;
    }

    uint64_t get_buffer_window_start() const
    {
        return __atomic_load_n(
            &event_ring_.header->control.buffer_window_start, __ATOMIC_ACQUIRE);
    }

    bool set_force_live(bool force)
    {
        std::swap(force_live_, force);
        return force;
    }

    std::string validate(EventSourceSpec const &) const override;

    [[nodiscard]] std::string
    init_iterator(EventIterator *, EventSourceSpec const &) const override;

private:
    std::filesystem::path origin_path_;
    int ring_fd_;
    EventRingLiveness initial_liveness_;
    bool force_live_;
    monad_event_ring event_ring_;
};

class EventCaptureFile : public EventSourceFile
{
public:
    EventCaptureFile() = delete;
    EventCaptureFile(EventCaptureFile const &) = delete;
    EventCaptureFile(EventCaptureFile &&) noexcept;
    ~EventCaptureFile() override;

    explicit EventCaptureFile(
        std::filesystem::path origin_path, int evcap_fd,
        monad_evcap_reader *evcap_reader)
        : origin_path_{std::move(origin_path)}
        , evcap_fd_{evcap_fd}
        , evcap_reader_{evcap_reader}
    {
    }

    std::string describe() const override;

    std::filesystem::path const &get_origin_path() const override
    {
        return origin_path_;
    }

    int get_file_descriptor() const override
    {
        return evcap_fd_;
    }

    Type get_type() const override
    {
        return Type::EventCaptureFile;
    }

    bool is_finalized() const override
    {
        return true;
    }

    bool is_interactive() const override
    {
        return false;
    }

    std::string validate(EventSourceSpec const &) const override;

    [[nodiscard]] std::string
    init_iterator(EventIterator *, EventSourceSpec const &) const override;

    monad_evcap_reader const *get_reader() const
    {
        return evcap_reader_;
    }

private:
    std::filesystem::path origin_path_;
    int evcap_fd_;
    monad_evcap_reader *evcap_reader_;
};

class BlockArchiveDirectory : public EventSourceFile
{
public:
    BlockArchiveDirectory() = delete;
    BlockArchiveDirectory(BlockArchiveDirectory const &) = delete;
    BlockArchiveDirectory(BlockArchiveDirectory &&) noexcept;
    ~BlockArchiveDirectory() override;

    explicit BlockArchiveDirectory(
        std::filesystem::path origin_path, int archive_fd,
        monad_bcap_archive *archive)
        : origin_path_{std::move(origin_path)}
        , archive_fd_{archive_fd}
        , archive_{archive}
    {
    }

    std::string describe() const override;

    std::filesystem::path const &get_origin_path() const override
    {
        return origin_path_;
    }

    int get_file_descriptor() const override
    {
        return archive_fd_;
    }

    Type get_type() const override
    {
        return Type::BlockArchiveDirectory;
    }

    bool is_finalized() const override
    {
        return true;
    }

    bool is_interactive() const override
    {
        return false;
    }

    std::string validate(EventSourceSpec const &) const override;

    [[nodiscard]] std::string
    init_iterator(EventIterator *, EventSourceSpec const &) const override;

    monad_bcap_archive const *get_block_archive() const
    {
        return archive_;
    }

private:
    std::filesystem::path origin_path_;
    int archive_fd_;
    monad_bcap_archive *archive_;
};

struct ResolvedCaptureSections
{
    monad_evcap_section_desc const *resolved_sd;
    monad_evcap_section_desc const *schema_sd;
};

std::optional<ResolvedCaptureSections> lookup_capture_section(
    EventSourceFile::Type, monad_evcap_reader const *,
    EventSourceQuery const &);
