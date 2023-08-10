# Modifications to the Original Code (or portions thereof):
# Monad: 2023
# - Fit naming and dependency management conventions of Monad
# Original Code is licensed under the Apache 2.0 License
# monad: Fast Ethereum Virtual Machine implementation
# Copyright 2022 The monad Authors.
# SPDX-License-Identifier: Apache-2.0
#

find_package(nlohmann_json CONFIG REQUIRED)
find_package(CLI11 CONFIG REQUIRED)

add_library(monad-statetestutils STATIC)
add_library(monad::statetestutils ALIAS monad-statetestutils)
target_compile_features(monad-statetestutils PUBLIC cxx_std_20)
target_link_libraries(monad-statetestutils PRIVATE monad nlohmann_json::nlohmann_json)
target_include_directories(monad-statetestutils PRIVATE ${monad_private_include_dir})
target_sources(
    monad-statetestutils PRIVATE
    statetest.hpp
    statetest_loader.cpp
    statetest_logs_hash.cpp
)

add_executable(monad-ethereum-statetest)
target_link_libraries(monad-ethereum-statetest PRIVATE monad::statetestutils monad GTest::gtest)
target_include_directories(monad-ethereum-statetest PRIVATE ${monad_private_include_dir})
target_sources(
    monad-ethereum-statetest PRIVATE
    statetest.cpp
    statetest_runner.cpp
)
target_compile_definitions(monad-ethereum-statetest PUBLIC GTEST_HAS_EXCEPTIONS)
