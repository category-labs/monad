/* libmonad_xla.so exports only its C API: none of XLA's, LLVM's, Abseil's or
   protobuf's symbols, which would clash with the copies of LLVM that IREE and
   Halide bring into the same process */
MONAD_XLA_1.0 {
  global:
    monad_xla_*;
  local:
    *;
};
