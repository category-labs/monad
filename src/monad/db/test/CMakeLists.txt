add_unit_test(
    # TODO: disable logging again when behave features are switched over to use
    # replay_ethereum. For now, this needs to be enabled for those behave tests
    # to pass
    ENABLE_LOGGING
    TARGET
    monad-dbtests
    SOURCES
    block_db.cpp
    db.cpp
    LIBRARIES
    monad
)
