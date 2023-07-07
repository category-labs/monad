add_unit_test(
    # ENABLE_LOGGING
    TARGET
    monad-statetests
    SOURCES
    account_state.cpp
    code_state.cpp
    datum.cpp
    state.cpp
    value_state.cpp
    LIBRARIES
    monad
)
