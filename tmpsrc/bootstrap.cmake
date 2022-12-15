include(third_party/evmone/cmake/cable/HunterGate.cmake)
if(NOT CMAKE_TOOLCHAIN_FILE)
  set(CMAKE_TOOLCHAIN_FILE ${CMAKE_CURRENT_SOURCE_DIR}/tmpsrc/third_party/silkworm/cmake/toolchain/cxx20.cmake CACHE FILEPATH "" FORCE)
endif()
HunterGate(
  URL "https://github.com/cpp-pm/hunter/archive/v0.24.3.tar.gz"
  SHA1 "10738b59e539818a01090e64c2d09896247530c7"
  FILEPATH "${CMAKE_SOURCE_DIR}/tmpsrc/third_party/silkworm/cmake/Hunter/config.cmake"
)
