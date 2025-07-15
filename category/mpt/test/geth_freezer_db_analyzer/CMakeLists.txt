# geth freezer db analyser
add_executable(geth_freezer_db_analyzer "geth_freezer_db_analyzer.cpp")
monad_compile_options(geth_freezer_db_analyzer)
target_link_libraries(geth_freezer_db_analyzer PUBLIC monad_core CLI11::CLI11)
find_library(libsnappy NAMES "snappy" QUIET)
if(libsnappy)
  target_link_libraries(geth_freezer_db_analyzer PUBLIC ${libsnappy})
endif()
