enable_language(C)

add_library(monad-vm-core STATIC)

target_sources(monad-vm-core PRIVATE
    "src/monad/vm/core/assert.cpp"
    "src/monad/vm/core/assert.h"
    "src/monad/vm/core/cases.hpp"
)

monad_compile_options(monad-vm-core)

target_include_directories(monad-vm-core
    PUBLIC src/
)

add_library(monad-vm::monad-vm-core ALIAS monad-vm-core)