add_unit_test(
    TARGET
    monad-executionethtests
    SOURCES
    fork_traits.cpp
    genesis.cpp
    # replay_eth_block_db.cpp // TODO: Comment back once ReplayBlockDb is refactored
    static_precompiles.cpp
    LIBRARIES
    monad
)
