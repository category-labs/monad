#include <monad/core/assert.h>
#include <monad/core/likely.h>
#include <monad/db/db_snapshot_filesystem.h>

#include <ankerl/unordered_dense.h>

#include <fcntl.h>
#include <filesystem>
#include <format>
#include <fstream>
#include <linux/mman.h>
#include <sys/mman.h>

struct monad_db_snapshot_filesystem_write_user_context
{
    std::filesystem::path root;
    ankerl::unordered_dense::map<uint64_t, std::array<std::ofstream, 4>>
        shard_to_stream;

    explicit monad_db_snapshot_filesystem_write_user_context(
        std::filesystem::path const root)
        : root{root}
    {
    }
};

monad_db_snapshot_filesystem_write_user_context *
monad_db_snapshot_filesystem_write_user_context_create(
    char const *const root, uint64_t const block)
{
    std::filesystem::path const snapshot{
        std::filesystem::path{root} / std::to_string(block)};
    MONAD_ASSERT_PRINTF(
        std::filesystem::create_directories(snapshot),
        "snapshot failed, %s already exists!",
        snapshot.c_str());
    return new monad_db_snapshot_filesystem_write_user_context{snapshot};
}

void monad_db_snapshot_filesystem_write_user_context_destroy(
    monad_db_snapshot_filesystem_write_user_context *context)
{
    delete context;
}

uint64_t monad_db_snapshot_write_filesystem(
    uint64_t const shard, monad_snapshot_type const type,
    unsigned char const *const bytes, size_t const len, void *const user)
{
    auto *const context =
        reinterpret_cast<monad_db_snapshot_filesystem_write_user_context *>(
            user);
    if (MONAD_UNLIKELY(!context->shard_to_stream.contains(shard))) {
        auto const shard_dir = context->root / std::to_string(shard);
        MONAD_ASSERT(std::filesystem::create_directory(shard_dir));
        auto const [it, success] = context->shard_to_stream.emplace(
            shard, std::array<std::ofstream, 4>{});
        MONAD_ASSERT(success);
        constexpr std::array files = {
            "eth_header", "account", "storage", "code"};
        for (size_t i = 0; i < it->second.size(); ++i) {
            auto &stream = it->second.at(i);
            std::filesystem::path const path = shard_dir / files[i];
            stream.open(path, std::ios::binary | std::ios::out);
            MONAD_ASSERT_PRINTF(
                stream.is_open(), "failed to open %s", path.c_str());
        }
    }

    std::ofstream &out = context->shard_to_stream.at(shard).at(type);
    auto const before = out.tellp();
    out.write(
        reinterpret_cast<char const *>(bytes),
        static_cast<std::streamsize>(len));
    MONAD_ASSERT(out.good());
    return static_cast<uint64_t>(out.tellp() - before);
}

void monad_db_snapshot_load_filesystem(
    char const *const *const dbname_paths, size_t const len,
    unsigned const sq_thread_cpu, char const *const snapshot_dir,
    uint64_t const block)
{
    std::filesystem::path const root{std::format("{}/{}", snapshot_dir, block)};
    MONAD_ASSERT(std::filesystem::is_directory(root));
    monad_db_snapshot_loader *const loader = monad_db_snapshot_loader_create(
        block, dbname_paths, len, sq_thread_cpu);

    auto const do_mmap = [](std::filesystem::path const file) {
        MONAD_ASSERT(std::filesystem::is_regular_file(file));
        int fd = open(file.c_str(), O_RDONLY);
        MONAD_ASSERT(fd != -1);

        unsigned long const size = std::filesystem::file_size(file);
        void *data = nullptr;
        if (size) {
            data = mmap(nullptr, size, PROT_READ, MAP_SHARED, fd, 0);
            MONAD_ASSERT(data != MAP_FAILED);
            // optimize for sequential accesses
            MONAD_ASSERT(madvise(data, size, MADV_SEQUENTIAL) == 0);
        }
        return std::make_tuple(
            fd, reinterpret_cast<unsigned char const *>(data), size);
    };

    for (auto const &dir : std::filesystem::directory_iterator{root}) {
        uint64_t const shard = std::stoull(dir.path().stem());
        auto const [eth_header_fd, eth_header, eth_header_len] =
            do_mmap(dir.path() / "eth_header");
        auto const [account_fd, account, account_len] =
            do_mmap(dir.path() / "account");
        auto const [storage_fd, storage, storage_len] =
            do_mmap(dir.path() / "storage");
        auto const [code_fd, code, code_len] = do_mmap(dir.path() / "code");
        monad_db_snapshot_loader_load(
            loader,
            shard,
            eth_header,
            eth_header_len,
            account,
            account_len,
            storage,
            storage_len,
            code,
            code_len);
        if (eth_header) {
            munmap((void *)eth_header, eth_header_len);
        }
        if (account) {
            munmap((void *)account, account_len);
        }
        if (storage) {
            munmap((void *)storage, storage_len);
        }
        if (code) {
            munmap((void *)code, code_len);
        }
        close(eth_header_fd);
        close(account_fd);
        close(storage_fd);
        close(code_fd);
    }

    monad_db_snapshot_loader_destroy(loader);
}
