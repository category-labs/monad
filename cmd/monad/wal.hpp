#pragma once

#include <category/core/bytes.hpp>
#include <category/core/config.hpp>
#include <category/execution/monad/core/monad_block.hpp>

#include <evmc/evmc.h>

#include <cstdint>
#include <filesystem>
#include <fstream>
#include <optional>
#include <variant>

MONAD_NAMESPACE_BEGIN

struct MonadChain;

enum class WalAction : uint8_t
{
    PROPOSE = 0,
    FINALIZE = 1,
};

static_assert(sizeof(WalAction) == 1);
static_assert(alignof(WalAction) == 1);

struct WalEntry
{
    WalAction action;
    bytes32_t id;
};

static_assert(sizeof(WalEntry) == 33);
static_assert(alignof(WalEntry) == 1);

class WalReader
{
    MonadChain const &chain_;
    std::ifstream cursor_;
    std::filesystem::path ledger_dir_;
    std::filesystem::path header_dir_;
    std::filesystem::path bodies_dir_;

public:
    struct Result
    {
        WalAction action;
        bytes32_t block_id;
        std::variant<MonadConsensusBlockHeaderV0, MonadConsensusBlockHeaderV1>
            header;
        MonadConsensusBlockBody body;
    };

    WalReader(MonadChain const &, std::filesystem::path const &ledger_dir);

    std::optional<Result> next();
};

class WalWriter
{
    std::filesystem::path wal_path_;
    std::ofstream cursor_;

public:
    WalWriter(std::filesystem::path const &ledger_dir);

    void write(WalAction action, bytes32_t const &block_id);
};

MONAD_NAMESPACE_END
