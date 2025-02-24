#pragma once

#include <monad/config.hpp>
#include <monad/core/bytes.hpp>
#include <monad/core/monad_block.hpp>

#include <evmc/evmc.h>

#include <filesystem>
#include <fstream>
#include <optional>

MONAD_NAMESPACE_BEGIN

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
    struct evmc_bytes32 id;
};

static_assert(sizeof(WalEntry) == 33);
static_assert(alignof(WalEntry) == 1);

class WalReader
{
    std::ifstream cursor_;
    std::filesystem::path ledger_dir_;

public:
    struct Result
    {
        WalAction action;
        MonadConsensusBlockHeader header;
        MonadConsensusBlockBody body;
        bytes32_t bft_block_id;
    };

    WalReader(std::filesystem::path const &ledger_dir);

    std::optional<Result> next();

    bool rewind_to(WalEntry const &);
};

MONAD_NAMESPACE_END
