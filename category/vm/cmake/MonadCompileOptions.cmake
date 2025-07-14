if(MONAD_COMPILER_STANDALONE)
  # Excerpted directly from:
  #   https://github.com/monad-crypto/monad/blob/main/CMakeLists.txt#L18
  # in the interests of upstreaming this project into the core Monad monorepo.
  function(monad_compile_options target)
    set_property(TARGET ${target} PROPERTY C_STANDARD 23)
    set_property(TARGET ${target} PROPERTY C_STANDARD_REQUIRED ON)
    set_property(TARGET ${target} PROPERTY CXX_STANDARD 23)
    set_property(TARGET ${target} PROPERTY CXX_STANDARD_REQUIRED ON)

    target_compile_options(${target} PRIVATE -Wall -Wextra -Wconversion -Werror)

    target_compile_options(${target} PRIVATE -mavx2)

    target_compile_options(
      ${target} PRIVATE $<$<CXX_COMPILER_ID:GNU>:-Wno-missing-field-initializers>)

    target_compile_options(
      ${target}
      PUBLIC $<$<CXX_COMPILER_ID:GNU>:-Wno-attributes=clang::no_sanitize>)
    
    if(MONAD_COMPILER_DUMP_ASM)
      target_compile_options(${target} PRIVATE -save-temps=obj -g -fverbose-asm -Wno-error)

      add_custom_command(TARGET ${target} POST_BUILD
          COMMAND ${CMAKE_COMMAND} -E make_directory "${CMAKE_BINARY_DIR}/asm"
          COMMAND ${CMAKE_COMMAND} -E echo "Copying .s files to build/asm/"
          COMMAND ${CMAKE_SOURCE_DIR}/scripts/copy_s_files.sh
            "${CMAKE_BINARY_DIR}" "${CMAKE_BINARY_DIR}/asm"
      )
    endif()
  endfunction()
endif()
