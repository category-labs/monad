add_library(triedb-driver "triedb.cpp")
monad_compile_options(triedb-driver)
target_link_libraries(triedb-driver PRIVATE monad_trie)
