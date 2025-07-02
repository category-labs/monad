function(check_debug_flags var)
  if(${var} MATCHES "-g$" OR ${var} MATCHES "-ggdb")
    message(FATAL_ERROR "Unwanted debug flags (-g or -ggdb) found in ${var}. Not permitted in release build")
  endif()
endfunction()

check_debug_flags(CMAKE_C_FLAGS_INIT)
check_debug_flags(CMAKE_CXX_FLAGS_INIT)

# eth_call.cpp and quill have issues with CMAKE_BUILD_TYPE=Release. Something to
# do with -O3. Previously, we built with RelWithDebInfo, which is -O2.
set(CMAKE_C_FLAGS_RELEASE "-DNDEBUG -Wall -Wextra -Wfatal-errors -O2 -g1")
set(CMAKE_CXX_FLAGS_RELEASE "-DNDEBUG -Wall -Wextra -Wfatal-errors -O2 -g1")
