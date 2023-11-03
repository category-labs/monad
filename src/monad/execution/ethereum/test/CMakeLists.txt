add_unit_test(
    TARGET
    monad-executionethtests
    SOURCES
    genesis.cpp
    # replay_eth_block_db.cpp // TODO: Comment back once ReplayBlockDb is refactored
    static_precompiles.cpp
    LIBRARIES
    monad
)
