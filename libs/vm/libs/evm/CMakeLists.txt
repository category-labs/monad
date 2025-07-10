add_library(monad-vm-evm STATIC)

set_target_properties(monad-vm-evm PROPERTIES LINKER_LANGUAGE CXX)

target_sources(monad-vm-evm PRIVATE
    "src/monad/vm/evm/opcodes.hpp"
    "src/monad/vm/evm/opcodes_xmacro.hpp"
)

target_include_directories(monad-vm-evm
    PUBLIC src
)

target_link_libraries(monad-vm-evm
    PUBLIC evmc::evmc
    PUBLIC monad-vm::monad-vm-core
)

# test 2

add_library(monad-vm::monad-vm-evm ALIAS monad-vm-evm)