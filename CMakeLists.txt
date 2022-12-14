cmake_minimum_required(VERSION 3.20)

project(monad)

############
### deps
############

find_package(Boost REQUIRED)


############
### opts
############

function(monad_compile_options target)
    set_property(TARGET ${target} PROPERTY C_STANDARD 11)
    set_property(TARGET ${target} PROPERTY C_STANDARD_REQUIRED ON)
    set_property(TARGET ${target} PROPERTY CXX_STANDARD 20)
    set_property(TARGET ${target} PROPERTY CXX_STANDARD_REQUIRED ON)
    target_compile_options(${target} PRIVATE -Wall -Wextra -Werror)
endfunction()


############
### libs
############

# monad

add_library(monad STATIC
    # core
    ${PROJECT_SOURCE_DIR}/include/monad/core/assert.h
    ${PROJECT_SOURCE_DIR}/include/monad/core/likely.h
    ${PROJECT_SOURCE_DIR}/src/monad/core/assert.c
)
target_include_directories(monad
    PUBLIC ${PROJECT_SOURCE_DIR}/include
    PRIVATE ${Boost_INCLUDE_DIRS}
)
target_link_options(monad
    PRIVATE LINKER:-z,defs
)
monad_compile_options(monad)
