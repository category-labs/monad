#include <monad/execution/blockchain.hpp>

#include <silkworm/consensus/engine.hpp>
#include <silkworm/execution/processor.hpp>

#include <string>

MONAD_NAMESPACE_BEGIN

using ExecutionProcessor = silkworm::ExecutionProcessor;

static_assert(sizeof(ExecutionProcessor) == 512);

Blockchain::Blockchain(State &state, ChainConfig const &config)
    : state_{state}
    , config_{config}
    , engine_{silkworm::consensus::engine_factory(config_)}
{
}

Blockchain::~Blockchain() {}

ValidationResult Blockchain::pre_validate_block(Block const &block)
{
    return engine_->pre_validate_block(block, state_);
}

ValidationResult
Blockchain::execute_block(Block &block, std::vector<Receipt> &receipts)
{
    ExecutionProcessor processor{block, *engine_, state_, config_};

    return processor.execute_and_write_block(receipts);
}

MONAD_NAMESPACE_END
