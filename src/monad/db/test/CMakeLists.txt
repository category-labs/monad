add_unit_test(
    # ENABLE_LOGGING
    TARGET
    monad-dbtests
    SOURCES
    block_db.cpp
    db.cpp
    LIBRARIES
    monad
)
