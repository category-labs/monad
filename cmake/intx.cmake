add_library(intx INTERFACE)
add_library(intx::intx ALIAS intx)
target_compile_features(intx INTERFACE cxx_std_20)
target_include_directories(intx INTERFACE ${MONAD_THIRD_PARTY}/intx/include)
