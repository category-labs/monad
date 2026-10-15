#include <cstdlib>
#include <cstdio>
extern "C" [[noreturn]] void zkvm_halt(int s) { std::printf("zkvm_halt(%d)\n", s); std::abort(); }
