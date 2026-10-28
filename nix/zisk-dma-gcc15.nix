# Adapt only context lines: GCC 15 added declarations/options and moved setmem.
# Keep the vendored GCC 14 patch and its code changes intact.
{ lib }:
let
  original = builtins.readFile
    ../zkvm/toolchain/zisk-dma-gcc/0001-riscv-zisk-dma-lowering-14.3.0.patch;
  context = lines: lib.concatMapStrings (line: " ${line}\n") lines;
  before = [
    (context [
      ";; Expand in-line code to clear the instruction cache between operand[0] and"
      ";; operand[1]." ''(define_expand "clear_cache"''
    ])
    (context [
      "mtls-dialect="
      "Target RejectNegative Joined Enum(tls_type) Var(riscv_tls_dialect) Init(TLS_TRADITIONAL) Save"
      "Specify TLS dialect."
    ])
    " \n /* Routines implemented in riscv-string.c.  */\n extern bool riscv_expand_block_move"
    " \n /* Information about one CPU we know about.  */\n struct riscv_cpu_info {\n"
  ];
  after = [
    (context [
      ";; Fill memory with constant byte."
      ";; Argument 0 is the destination" ";; Argument 1 is the constant byte"
    ])
    (context [
      "mautovec-segment" "Target Integer Var(riscv_mautovec_segment) Init(1)"
      "Enable (default) or disable generation of vector segment load/store instructions."
    ])
    " /* Routines implemented in riscv-string.c.  */\n extern bool riscv_expand_block_compare (rtx, rtx, rtx, rtx);\n extern bool riscv_expand_block_move"
    " extern bool riscv_expand_block_clear (rtx, rtx);\n \n /* Information about one CPU we know about.  */\n"
  ];
in
assert builtins.all (context: lib.hasInfix context original) before;
builtins.toFile "riscv-zisk-dma-gcc15.patch"
  (builtins.replaceStrings before after original)
