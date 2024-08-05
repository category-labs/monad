#pragma once

#include "config.hpp"

#include <monad/async/io.hpp>
#include <monad/mpt/trie.hpp>

#include <filesystem>

MONAD_ASYNC_NAMESPACE_BEGIN

inline std::filesystem::path create_temp_file(int64_t const size)
{
    std::filesystem::path const filename{
        working_temporary_directory() / "XXXXXX"};
    int const fd = ::mkstemp((char *)filename.native().data());
    MONAD_ASSERT(fd != -1);
    auto unfd = monad::make_scope_exit([fd]() noexcept { ::close(fd); });
    MONAD_ASSERT(-1 != ::ftruncate(fd, size * 1024 * 1024 * 1024));
    return filename;
}

inline void initialize_storage_pool(std::filesystem::path const &filename)
{
    MONAD_ASSERT(std::filesystem::exists(filename));
    // initialize storage pool
    auto pool = storage_pool{{&filename, 1}, storage_pool::mode::truncate};
    // intialize metadata
    monad::io::Ring ring(1);
    monad::io::Buffers rwbuf = monad::io::make_buffers_for_read_only(
        ring, 2, AsyncIO::MONAD_IO_BUFFERS_READ_SIZE);
    auto io = AsyncIO{pool, rwbuf};
    monad::mpt::UpdateAux<> aux(&io);
}

MONAD_ASYNC_NAMESPACE_END
