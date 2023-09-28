add_unit_test(
    TARGET
    monad-executiontests
    SOURCES
    # block_processor.cpp // TODO: Comment back once BP is refactored
    create_contract_address.cpp
    evm.cpp
    evmc_host.cpp
    evmone_baseline_interpreter.cpp
    # replay_block_db.cpp // TODO: Comment back once ReplayBlockDb is refactored
    transaction_processor.cpp
    # transaction_processor_data.cpp // TODO: Comment back once TransactionProcessorData is refactored
    validation.cpp
    LIBRARIES
    monad
    evmone
)
