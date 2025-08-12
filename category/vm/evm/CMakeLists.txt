add_library(monad-vm-evm OBJECT)

set_target_properties(monad-vm-evm PROPERTIES LINKER_LANGUAGE CXX)

target_sources(monad-vm-evm PRIVATE
    "opcodes.hpp"
    "opcodes_xmacro.hpp"
)

target_include_directories(monad-vm-evm
    PUBLIC ${CATEGORY_MAIN_DIR}
)

target_link_libraries(monad-vm-evm
    PUBLIC evmc::evmc
    PUBLIC monad-vm::monad-vm-core
)

add_library(monad-vm::monad-vm-evm ALIAS monad-vm-evm)
