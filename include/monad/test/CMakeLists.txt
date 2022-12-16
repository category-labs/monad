project(monad-testutils)

add_library(${PROJECT_NAME} STATIC
    ${PROJECT_SOURCE_DIR}/utils.hpp
)

set_target_properties(${PROJECT_NAME} PROPERTIES LINKER_LANGUAGE CXX)
