add_unit_test(
    TARGET
    monad-trielibtests
    SOURCES
    nibbles.cpp
    compact_encode.cpp
    node.cpp
    LIBRARIES
    monad)

add_unit_test(
    TARGET
    monad-singletrietests
    SOURCES
    single_trie.cpp
    LIBRARIES
    monad
)

add_unit_test(
    TARGET
    monad-multipletrietests
    SOURCES
    multiple_trie.cpp
    LIBRARIES
    monad
)
