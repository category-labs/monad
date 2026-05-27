function(monad_compile_options target)
  set_property(TARGET ${target} PROPERTY C_STANDARD 23)
  set_property(TARGET ${target} PROPERTY C_STANDARD_REQUIRED ON)
  set_property(TARGET ${target} PROPERTY CXX_STANDARD 23)
  set_property(TARGET ${target} PROPERTY CXX_STANDARD_REQUIRED ON)

  target_compile_options(${target} PRIVATE -Wall -Wextra -Wconversion -Werror)
  target_compile_definitions(${target} PUBLIC "_GNU_SOURCE")

  target_compile_options(
    ${target} PRIVATE $<$<CXX_COMPILER_ID:GNU>:-Wno-missing-field-initializers>)

  target_compile_options(${target} PRIVATE $<$<CONFIG:Debug>:-Og>)

  target_compile_definitions(${target} PUBLIC QUILL_ROOT_LOGGER_ONLY)

  if(MONAD_COMPILER_TESTING)
    target_compile_definitions(${target} PUBLIC "MONAD_COMPILER_TESTING=1")
    target_compile_definitions(${target} PUBLIC "MONAD_CORE_FORCE_DEBUG_ASSERT=1")
  endif()

  if(MONAD_COMPILER_STATS)
      target_compile_definitions(${target} PUBLIC "MONAD_COMPILER_STATS=1")
  endif()

  if(MONAD_COMPILER_HOT_PATH_STATS)
      target_compile_definitions(${target} PUBLIC "MONAD_COMPILER_HOT_PATH_STATS=1")
  endif()

  target_compile_options(
    ${target}
    PUBLIC $<$<CXX_COMPILER_ID:GNU>:-Wno-attributes=clang::no_sanitize>)

  # this is needed to turn off ranges support in nlohmann_json, because the
  # ranges standard header triggers a clang bug which is fixed in trunk but not
  # currently available to us
  # https://gcc.gnu.org/bugzilla//show_bug.cgi?id=109647
  target_compile_definitions(${target} PUBLIC "JSON_HAS_RANGES=0")

endfunction()
