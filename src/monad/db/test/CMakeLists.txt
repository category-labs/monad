add_unit_test(
    # ENABLE_LOGGING
    TARGET
    monad-dbtests
    SOURCES
    block_db.cpp
    trie_db.cpp
    LIBRARIES
    monad
)
