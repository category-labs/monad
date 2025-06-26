set(CMAKE_ASM_FLAGS_INIT "-march=haswell")
set(CMAKE_C_FLAGS_INIT "-march=haswell")
set(CMAKE_CXX_FLAGS_INIT "-march=haswell")

# eth_call.cpp and quill have issues with CMAKE_BUILD_TYPE=Release. Something to
# do with -O3. Previously, we built with RelWithDebInfo, which is -O2.
set(CMAKE_C_FLAGS_RELEASE "-DNDEBUG -Wall -Wextra -Wfatal-errors -O2 -g1")
set(CMAKE_CXX_FLAGS_RELEASE "-DNDEBUG -Wall -Wextra -Wfatal-errors -O2 -g1")
