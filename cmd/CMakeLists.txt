include_directories(${CMAKE_CURRENT_SOURCE_DIR})

find_package(CLI11 REQUIRED)

add_executable(
  monad
  monad/main.cpp
  monad/event.cpp
  monad/event.hpp
  monad/runloop_ethereum.cpp
  monad/runloop_ethereum.hpp
  monad/runloop_monad.cpp
  monad/runloop_monad.hpp)

monad_compile_options(monad)

target_link_libraries(monad PRIVATE monad_execution monad_statesync
                                    CLI11::CLI11)

if(DEFINED ENV{GIT_COMMIT_HASH})
  set(GIT_COMMIT_HASH $ENV{GIT_COMMIT_HASH})
else()
  execute_process(
    COMMAND git rev-parse HEAD
    WORKING_DIRECTORY ${CMAKE_SOURCE_DIR}
    OUTPUT_VARIABLE GIT_COMMIT_HASH
    OUTPUT_STRIP_TRAILING_WHITESPACE)
endif()

target_compile_definitions(monad PRIVATE GIT_COMMIT_HASH="${GIT_COMMIT_HASH}")
add_executable(monad_cli monad_cli.cpp)
monad_compile_options(monad_cli)
target_link_libraries(monad_cli PUBLIC monad_execution CLI11::CLI11)

add_executable(eventcap eventcap.cpp)
monad_compile_options(eventcap)
target_link_libraries(eventcap PRIVATE monad_event_client CLI11::CLI11)
target_compile_options(eventcap PRIVATE -Wno-missing-field-initializers)

add_executable(snapshot-rsm snapshot-rsm.cpp)
monad_compile_options(snapshot-rsm)
target_link_libraries(snapshot-rsm PRIVATE monad_core monad_event_client CLI11::CLI11 -lzstd)
target_compile_options(snapshot-rsm PRIVATE -Wno-missing-field-initializers)
