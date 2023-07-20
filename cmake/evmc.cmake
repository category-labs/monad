add_library(evmc INTERFACE)
add_library(evmc::evmc ALIAS evmc)
target_compile_features(evmc INTERFACE c_std_99)
target_include_directories(evmc INTERFACE ${MONAD_THIRD_PARTY}/evmc/include)

add_library(evmc_cpp INTERFACE)
add_library(evmc::evmc_cpp ALIAS evmc_cpp)
target_compile_features(evmc_cpp INTERFACE cxx_std_17)
target_include_directories(evmc_cpp INTERFACE ${MONAD_THIRD_PARTY}/evmc/include)
target_link_libraries(evmc_cpp INTERFACE evmc::evmc)

