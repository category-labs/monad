configure_file("build.rs.in" "${CMAKE_CURRENT_BINARY_DIR}/build.rs")

add_custom_target(
    copy_state_history_crate ALL
    COMMENT "Copy state_history"
    COMMAND cp -r "${PROJECT_SOURCE_DIR}/state_history"
            "${CMAKE_CURRENT_BINARY_DIR}"
    COMMAND ln -sf "${CMAKE_CURRENT_BINARY_DIR}/build.rs"
            "${CMAKE_CURRENT_BINARY_DIR}/state_history/build.rs"
    USES_TERMINAL VERBATIM
)

add_custom_target(
    state_history_crate ALL
    COMMENT "Building and running state_history"
    COMMAND "${PROJECT_SOURCE_DIR}/scripts/cargo/clean_build_and_run.sh"
    WORKING_DIRECTORY "${CMAKE_CURRENT_BINARY_DIR}/state_history"
    USES_TERMINAL VERBATIM
)
add_dependencies(state_history_crate copy_state_history_crate)
