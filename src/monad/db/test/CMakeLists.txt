add_unit_test(
  # ENABLE_LOGGING
  TARGET
  monad-dbtests
  SOURCES
  account_store.cpp
  block_db.cpp
  code_store.cpp
  datum.cpp
  state.cpp
  value_store.cpp
  trie_db.cpp
  LIBRARIES
  monad)
