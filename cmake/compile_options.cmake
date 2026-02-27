function(monad_compile_options target)
  set_property(TARGET ${target} PROPERTY C_STANDARD 23)
  set_property(TARGET ${target} PROPERTY C_STANDARD_REQUIRED ON)
  set_property(TARGET ${target} PROPERTY CXX_STANDARD 23)
  set_property(TARGET ${target} PROPERTY CXX_STANDARD_REQUIRED ON)

  target_compile_options(${target} PRIVATE -Wall -Wextra -Wconversion -Werror)
  target_compile_definitions(${target} PUBLIC "_GNU_SOURCE")

  target_compile_options(
    ${target} PRIVATE $<$<CXX_COMPILER_ID:GNU>:-Wno-missing-field-initializers>)

  if(MONAD_ZKVM)
    # GCC 15+ checks uninstantiated template bodies for errors (-Wtemplate-body).
    # This fires on constexpr-guarded AVX2 code paths that are never instantiated
    # on non-x86 targets.
    target_compile_options(
      ${target} PRIVATE $<$<CXX_COMPILER_ID:GNU>:-Wno-template-body>)

    # GCC 15+ warns when reference parameters are forwarded through musttail
    # calls. The interpreter's threaded dispatch passes references to objects
    # that live in earlier stack frames, not the current one, so this is safe.
    target_compile_options(
      ${target} PRIVATE $<$<CXX_COMPILER_ID:GNU>:-Wno-maybe-musttail-local-addr>)
  endif()

  target_compile_definitions(${target} PUBLIC QUILL_ROOT_LOGGER_ONLY)

  if(MONAD_COMPILER_TESTING)
    target_compile_definitions(${target} PUBLIC "MONAD_COMPILER_TESTING=1")
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

  if(MONAD_ZKVM)
    # NDEBUG is required because the bare-metal zkVM environment does not link
    # the C standard library, so __assert_func (used by assert()) is unavailable.
    target_compile_definitions(${target} PUBLIC MONAD_ZKVM NDEBUG)
  endif()
endfunction()
