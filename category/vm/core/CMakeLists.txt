enable_language(C)

add_library(monad-vm-core)

target_sources(monad-vm-core PRIVATE
    "assert.cpp"
    "assert.h"
    "cases.hpp"
)

monad_compile_options(monad-vm-core)

target_include_directories(monad-vm-core
    PUBLIC ${CATEGORY_MAIN_DIR}
)

add_library(monad-vm::monad-vm-core ALIAS monad-vm-core)
