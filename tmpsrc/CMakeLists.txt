############
### deps
############

add_subdirectory(tmpsrc/third_party/silkworm)


############
### opts
############


############
### libs
############

# monad

target_sources(monad
    PRIVATE
    # db
    ${PROJECT_SOURCE_DIR}/tmpsrc/include/monad/core/account.hpp
    ${PROJECT_SOURCE_DIR}/tmpsrc/include/monad/core/address.hpp
    ${PROJECT_SOURCE_DIR}/tmpsrc/include/monad/db/block_db.hpp
    ${PROJECT_SOURCE_DIR}/tmpsrc/include/monad/db/state_db.hpp
    ${PROJECT_SOURCE_DIR}/tmpsrc/include/monad/execution/blockchain.hpp
    ${PROJECT_SOURCE_DIR}/tmpsrc/include/monad/execution/execution.hpp
    ${PROJECT_SOURCE_DIR}/tmpsrc/include/monad/execution/hashstate.hpp
    ${PROJECT_SOURCE_DIR}/tmpsrc/include/monad/execution/interhash.hpp
    ${PROJECT_SOURCE_DIR}/tmpsrc/src/monad/db/block_db.cpp
    ${PROJECT_SOURCE_DIR}/tmpsrc/src/monad/db/state_db.cpp
    ${PROJECT_SOURCE_DIR}/tmpsrc/src/monad/execution/blockchain.cpp
    ${PROJECT_SOURCE_DIR}/tmpsrc/src/monad/execution/execution.cpp
    ${PROJECT_SOURCE_DIR}/tmpsrc/src/monad/execution/hashstate.cpp
    ${PROJECT_SOURCE_DIR}/tmpsrc/src/monad/execution/interhash.cpp
)
target_include_directories(monad
    PUBLIC ${PROJECT_SOURCE_DIR}/tmpsrc/include
)
target_link_libraries(monad
    PUBLIC silkworm_core
    PUBLIC silkworm_node
)

add_subdirectory(${PROJECT_SOURCE_DIR}/tmpsrc/cmd)
