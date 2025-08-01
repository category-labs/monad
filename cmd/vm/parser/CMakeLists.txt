add_executable(parser-tool)

target_sources(parser-tool PRIVATE
  parser_tool.cpp)

target_include_directories(parser-tool
  PUBLIC src/
)

target_link_libraries(parser-tool
  PRIVATE evmc::evmc
  PRIVATE evmone
  PRIVATE monad-vm::monad-vm-utils
  PRIVATE monad-vm::monad-vm-compiler
  PRIVATE CLI11::CLI11
)

monad_compile_options(parser-tool)
