add_library(monad-vm-fuzzing)

target_sources(monad-vm-fuzzing PRIVATE
  "generator/choice.hpp"
  "generator/generator.hpp"
  "generator/instruction_data.cpp"
  "generator/instruction_data.hpp"
)

monad_compile_options(monad-vm-fuzzing)

target_include_directories(monad-vm-fuzzing
  PUBLIC src/
)

target_link_libraries(monad-vm-fuzzing
  PUBLIC monad-vm::monad-vm-compiler
  PUBLIC monad-vm::monad-vm-core
  PUBLIC monad-vm::monad-vm-utils
)

add_library(monad-vm::monad-vm-fuzzing ALIAS monad-vm-fuzzing)
