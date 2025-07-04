function(monad_link_llvm target)
    llvm_config(${target}
       USE_SHARED true)

    # these options are needed to ignore the spurious ciso646 warning
    target_compile_options(${target} PRIVATE $<$<CXX_COMPILER_ID:GNU>:-Wno-cpp>)
    target_compile_options(${target} PRIVATE $<$<CXX_COMPILER_ID:Clang>:-Wno-\#warnings>)


    target_include_directories(${target}
        SYSTEM PRIVATE ${LLVM_INCLUDE_DIRS})
endfunction()
