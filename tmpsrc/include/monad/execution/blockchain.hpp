#pragma once

#include <monad/config.hpp>

#include <silkworm/consensus/validation.hpp>
#include <silkworm/types/receipt.hpp>

#include <memory>
#include <vector>

namespace silkworm
{
    struct Block;
    struct ChainConfig;
    class State;
}

namespace silkworm::consensus
{
    class IEngine;
}

MONAD_NAMESPACE_BEGIN

using Block = silkworm::Block;
using ChainConfig = silkworm::ChainConfig;
using IEngine = silkworm::consensus::IEngine;
using Receipt = silkworm::Receipt;
using State = silkworm::State;
using ValidationResult = silkworm::ValidationResult;

class Blockchain final
{
    State &state_;
    ChainConfig const& config_;
    std::unique_ptr<IEngine> const engine_;

public:
    Blockchain(State &, ChainConfig const&);

    Blockchain(Blockchain const &) = delete;
    Blockchain &operator=(Blockchain const &) = delete;

    ~Blockchain();

    ValidationResult pre_validate_block(Block const &);
    ValidationResult execute_block(Block &, std::vector<Receipt>&);
};

MONAD_NAMESPACE_END
