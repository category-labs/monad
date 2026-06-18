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

#include <category/core/assert.h>
#include <category/core/config.hpp>
#include <category/execution/ethereum/db/tar_file_db.hpp>

#include <algorithm>
#include <charconv>
#include <cstdint>
#include <cstring>
#include <fcntl.h>
#include <filesystem>
#include <memory>
#include <optional>
#include <string>
#include <string_view>
#include <system_error>
#include <unistd.h>
#include <unordered_map>
#include <utility>

MONAD_ANONYMOUS_NAMESPACE_BEGIN

constexpr size_t TAR_BLOCK = 512;

// USTAR header (POSIX.1-1988): 512 bytes, followed by payload padded to 512.
struct UstarHeader
{
    char name[100];
    char mode[8];
    char uid[8];
    char gid[8];
    char size[12];
    char mtime[12];
    char chksum[8];
    char typeflag;
    char linkname[100];
    char magic[6];
    char version[2];
    char uname[32];
    char gname[32];
    char devmajor[8];
    char devminor[8];
    char prefix[155];
    char pad[12];
};

static_assert(sizeof(UstarHeader) == TAR_BLOCK);

bool is_zero_block(UstarHeader const &h)
{
    auto bytes = std::as_bytes(std::span{&h, 1});

    return std::ranges::all_of(
        bytes, [](std::byte b) { return b == std::byte{0}; });
}

std::optional<uint64_t> parse_octal(char const *field, size_t n)
{
    uint64_t v = 0;
    bool any = false;
    for (size_t i = 0; i < n; ++i) {
        char const c = field[i];
        if (c == '\0' || c == ' ') {
            if (any) {
                break;
            }
            continue;
        }
        if (c < '0' || c > '7') {
            return std::nullopt;
        }
        v = (v << 3) | static_cast<uint64_t>(c - '0');
        any = true;
    }
    return v;
}

std::string read_name(UstarHeader const &h)
{
    std::string_view const name{h.name, ::strnlen(h.name, sizeof(h.name))};
    std::string_view const prefix{
        h.prefix, ::strnlen(h.prefix, sizeof(h.prefix))};
    if (prefix.empty()) {
        return std::string{name};
    }
    std::string out;
    out.reserve(prefix.size() + 1 + name.size());
    out.assign(prefix);
    out.push_back('/');
    out.append(name);
    return out;
}

MONAD_ANONYMOUS_NAMESPACE_END

MONAD_NAMESPACE_BEGIN

class TarFileDb::Impl
{
    struct Entry
    {
        off_t data_offset;
        uint64_t size;
    };

    using IndexMap = std::unordered_map<std::string, Entry>;

    std::filesystem::path root_;
    bool single_file_;

    // Lazy bucket cache; current_bucket_ == -1 means no fd is open.
    mutable int fd_{-1};
    mutable int64_t current_bucket_{-1};
    mutable IndexMap index_{};

    static bool build_index(int const fd, IndexMap &out)
    {
        UstarHeader h;
        off_t pos = 0;
        int zero_blocks = 0;
        while (true) {
            ssize_t const r = ::pread(fd, &h, sizeof(h), pos);
            if (r == 0) {
                break; // truncated archive - accept silently
            }
            if (r != static_cast<ssize_t>(sizeof(h))) {
                return false;
            }
            if (is_zero_block(h)) {
                ++zero_blocks;
                if (zero_blocks >= 2) {
                    break;
                }
                pos += static_cast<off_t>(TAR_BLOCK);
                continue;
            }
            zero_blocks = 0;

            auto const sz = parse_octal(h.size, sizeof(h.size));
            if (!sz.has_value()) {
                return false;
            }

            off_t const data_offset = pos + static_cast<off_t>(TAR_BLOCK);
            off_t const payload_blocks =
                (static_cast<off_t>(*sz) + static_cast<off_t>(TAR_BLOCK) - 1) /
                static_cast<off_t>(TAR_BLOCK);

            // Skip non-regular-file entries (directories, symlinks, long-name
            // and pax extension records). Block-number keys fit in the 100-
            // char ustar name field, so no extension headers are expected.
            char const t = h.typeflag;
            if (t == '\0' || t == '0') {
                // insert_or_assign so later entries shadow earlier ones,
                // matching `tar --append` semantics.
                out.insert_or_assign(read_name(h), Entry{data_offset, *sz});
            }

            pos = data_offset + payload_blocks * static_cast<off_t>(TAR_BLOCK);
        }
        return true;
    }

    void close_current() const
    {
        if (fd_ >= 0) {
            ::close(fd_);
            fd_ = -1;
        }
        index_.clear();
        current_bucket_ = -1;
    }

    bool open_bucket(int64_t const bucket) const
    {
        MONAD_ASSERT(!single_file_);
        // Build the new fd + index into locals first; only swap into the
        // member state once we know the new bucket is usable. Otherwise a
        // failure here would discard the cache and force the next get() in
        // the previously-open bucket to rebuild its index from scratch.
        auto const path = root_ / (std::to_string(bucket) + "M.tar");
        std::error_code ec;
        if (!std::filesystem::is_regular_file(path, ec)) {
            return false;
        }
        int const fd = ::open(path.c_str(), O_RDONLY | O_CLOEXEC);
        if (fd < 0) {
            return false;
        }
        IndexMap idx;
        if (!build_index(fd, idx)) {
            ::close(fd);
            return false;
        }
        close_current();
        fd_ = fd;
        current_bucket_ = bucket;
        index_ = std::move(idx);
        return true;
    }

public:
    explicit Impl(std::filesystem::path const &path)
        : root_{path}
        , single_file_{std::filesystem::is_regular_file(path)}
    {
        if (single_file_) {
            int const fd = ::open(path.c_str(), O_RDONLY | O_CLOEXEC);
            MONAD_ASSERT_PRINTF(fd >= 0, "cannot open tar %s", path.c_str());
            IndexMap idx;
            MONAD_ASSERT_PRINTF(
                build_index(fd, idx), "malformed tar %s", path.c_str());
            fd_ = fd;
            current_bucket_ = 0;
            index_ = std::move(idx);
        }
        else {
            MONAD_ASSERT_PRINTF(
                std::filesystem::is_directory(path),
                "not a tar file or directory: %s",
                path.c_str());
        }
    }

    ~Impl()
    {
        close_current();
    }

    std::optional<std::string> get(char const *const key) const
    {
        // Our entries are flat "14000000"-style keys. FileDb-fallback keys
        // like "14M/14000000" are not a thing in tar mode - reject cheaply.
        std::string_view const k{key};
        if (k.find('/') != std::string_view::npos) {
            return std::nullopt;
        }
        uint64_t num = 0;
        auto const [ptr, ec] =
            std::from_chars(k.data(), k.data() + k.size(), num);
        if (ec != std::errc{} || ptr != k.data() + k.size()) {
            return std::nullopt;
        }

        if (!single_file_) {
            auto const bucket = static_cast<int64_t>(num / 1'000'000);
            if (bucket != current_bucket_) {
                if (!open_bucket(bucket)) {
                    return std::nullopt;
                }
            }
        }

        auto const it = index_.find(std::string{k});
        if (it == index_.end()) {
            return std::nullopt;
        }
        std::string out;
        out.resize(it->second.size);
        ssize_t const r =
            ::pread(fd_, out.data(), it->second.size, it->second.data_offset);
        if (r != static_cast<ssize_t>(it->second.size)) {
            return std::nullopt;
        }
        return out;
    }
};

TarFileDb::TarFileDb(TarFileDb &&) noexcept = default;

TarFileDb::TarFileDb(std::filesystem::path const &p)
    : impl_{new Impl{p}}
{
}

TarFileDb::~TarFileDb() = default;

std::optional<std::string> TarFileDb::get(char const *const key) const
{
    return impl_->get(key);
}

bool TarFileDb::looks_like_tar_backed(std::filesystem::path const &p)
{
    std::error_code ec;
    if (std::filesystem::is_regular_file(p, ec)) {
        return p.extension() == ".tar";
    }
    if (!std::filesystem::is_directory(p, ec)) {
        return false;
    }
    // Assumes the block_db layout is exclusively tar files or exclusively
    // bare numbered block files. Early-exit on any files-mode evidence
    // (subdirectory or all-digit filename) keeps autodetect cheap when
    // pointed at a directory of millions of bare numbered files; the cost
    // is that mixed layouts may be misdetected since directory_iterator
    // order is unspecified. Pass BlockDbFormat::Tar explicitly to skip
    // autodetect.
    for (auto const &entry : std::filesystem::directory_iterator{p, ec}) {
        if (ec) {
            return false;
        }
        auto const name = entry.path().filename().string();

        if (entry.is_directory(ec) ||
            (!name.empty() &&
             std::all_of(name.begin(), name.end(), [](char const c) {
                 return c >= '0' && c <= '9';
             }))) {
            return false;
        }

        if (!entry.is_regular_file(ec)) {
            continue;
        }
        if (entry.path().extension() != ".tar") {
            continue;
        }
        auto const stem = entry.path().stem().string();
        if (stem.size() < 2 || stem.back() != 'M') {
            continue;
        }
        auto const digits = std::string_view{stem}.substr(0, stem.size() - 1);
        if (std::all_of(digits.begin(), digits.end(), [](char const c) {
                return c >= '0' && c <= '9';
            })) {
            return true;
        }
    }
    return false;
}

MONAD_NAMESPACE_END
