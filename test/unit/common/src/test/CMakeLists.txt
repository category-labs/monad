add_unit_test(
    TARGET
    monad-unittestcommontests
    SOURCES
    ${PROJECT_SOURCE_DIR}/test/unit/common/src/test/dump_state_from_db.cpp
    LIBRARIES
    monad_unit_test_common
    nlohmann_json::nlohmann_json)