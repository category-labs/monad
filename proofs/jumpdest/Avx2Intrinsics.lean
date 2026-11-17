import Types

/-! Executable value semantics for the intrinsics used by the jumpdest scan.
    Linked Clang documentation gives the intrinsic semantics and instruction mappings.
    Mnemonics describe the operations, not guaranteed compiler output: constants,
    constructors, and casts can be folded or lowered differently. For 128-bit
    intrinsics, V-prefixed mnemonics denote their VEX-encoded AVX forms.
    See also the [Intel Intrinsics Guide](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html)
    and [Intel SDM, Volume 2](https://www.intel.com/content/www/us/en/developer/articles/technical/intel-sdm.html).
    These definitions are not connected by a proof to Intel's ISA or x86lean. -/
namespace Jumpdest.Avx2

abbrev __m128i := BitVec 128
abbrev __m256i := BitVec 256

def byte (v : BitVec n) (i : Nat) : Byte := v.extractLsb' (8 * i) 8

/-- Byte zero occupies the least significant eight bits. -/
def bytes (n : Nat) (f : Nat → Byte) : BitVec n :=
  (List.range (n / 8)).foldl
    (fun acc i => acc ||| ((f i).zeroExtend n <<< (8 * i))) 0

def zipBytes (f : Byte → Byte → Byte) (a b : BitVec n) : BitVec n :=
  bytes n fun i => f (byte a i) (byte b i)

def truthMask (p : Bool) : Byte := if p then 0xff else 0

/-- Byte broadcast constructor; no single required instruction.
    [Clang documentation](https://clang.llvm.org/doxygen/emmintrin_8h.html#afc9d7da41f9e468293a2cfd07888166f). -/
def _mm_set1_epi8 (a : Byte) : __m128i := bytes 128 fun _ => a

/-- Byte broadcast constructor. Clang documents VPSHUFB + VINSERTF128; the
    emitted sequence is compiler-dependent.
    [Clang documentation](https://clang.llvm.org/doxygen/avxintrin_8h.html#ae3fb59a8658d3ea5ef78dfa4a1caf222). -/
def _mm256_set1_epi8 (a : Byte) : __m256i := bytes 256 fun _ => a

/-- Vector constructor; no single required instruction.
    The first argument element is byte zero, as with Intel's setr intrinsic.
    [Clang documentation](https://clang.llvm.org/doxygen/avxintrin_8h.html#a98349cabb197418813d714c8dc5a1b1d). -/
def _mm256_setr_epi8 (a : Vector Byte 32) : __m256i := bytes 256 fun i => a.getD i 0

/-- VMOVDQU (YMM): unaligned 256-bit load.
    Array-plus-byte-offset representation of a pointer. No alignment requirement.
    Deviation: an out-of-range read returns zero here, where C++ has undefined
    behaviour. The model is therefore faithful only when all 32 bytes are in
    range, a precondition this definition does not enforce. `jumpdests_avx2`
    meets it: the last index read is at most code_size + 30, and the shared
    `pad` supplies 33 trailing zero bytes.
    [Clang documentation](https://clang.llvm.org/doxygen/avxintrin_8h.html#ac5e0ec763ca41c3d1349242dfc8b7ba0). -/
def _mm256_loadu_si256 (code : Array Byte) (offset : Nat) : __m256i :=
  bytes 256 fun i => code.getD (offset + i) 0

/-- Low-half cast; no machine instruction is required.
    [Clang documentation](https://clang.llvm.org/doxygen/avxintrin_8h.html#ae4b6af305b21ad75e0ffaa2e1ec856f7). -/
def _mm256_castsi256_si128 (a : __m256i) : __m128i := a.extractLsb' 0 128

/-- VEXTRACTI128: immediate bit 0 selects the 128-bit half.
    imm models the bit pattern of C's 32-bit int. C++ requires a compile-time
    immediate; this value-level model does not enforce that restriction.
    [Clang documentation](https://clang.llvm.org/doxygen/avx2intrin_8h.html#aad58b51492bbbb175bcafd021585d930). -/
def _mm256_extracti128_si256 (a : __m256i) (imm : BitVec 32) : __m128i :=
  a.extractLsb' (if imm.getLsbD 0 then 128 else 0) 128

/-- Concatenate halves; Clang documents VINSERTF128 as the lowering.
    The argument order is high half, then low half.
    [Clang documentation](https://clang.llvm.org/doxygen/avxintrin_8h.html#aec456a04f2f9937ea8d673428db47a4c). -/
def _mm256_set_m128i (hi lo : __m128i) : __m256i := hi ++ lo

/-- VPADDB (YMM): wrapping byte addition.
    [Clang documentation](https://clang.llvm.org/doxygen/avx2intrin_8h.html#a7aa1c61703591f6572722d01e3c371b2). -/
def _mm256_add_epi8 (a b : __m256i) : __m256i := zipBytes (· + ·) a b

/-- VPSUBB (XMM), or legacy PSUBB: wrapping byte subtraction.
    [Clang documentation](https://clang.llvm.org/doxygen/emmintrin_8h.html#ac1eb656086c60d309fde37490a736414). -/
def _mm_sub_epi8 (a b : __m128i) : __m128i := zipBytes (· - ·) a b

/-- VPMAXSB (YMM): signed byte maximum; bytes 0x80..0xff are negative.
    [Clang documentation](https://clang.llvm.org/doxygen/avx2intrin_8h.html#ae404f3ed3150ebef98732fe532bb751c). -/
def _mm256_max_epi8 (a b : __m256i) : __m256i :=
  zipBytes (fun x y => if x.sle y then y else x) a b

/-- VPMAXUB (YMM): unsigned byte maximum.
    [Clang documentation](https://clang.llvm.org/doxygen/avx2intrin_8h.html#ac21a656e223a3e13c840eb7774e26176). -/
def _mm256_max_epu8 (a b : __m256i) : __m256i :=
  zipBytes (fun x y => if x ≤ y then y else x) a b

/-- VPMAXUB (XMM), or legacy PMAXUB: unsigned byte maximum.
    [Clang documentation](https://clang.llvm.org/doxygen/emmintrin_8h.html#a1ac4b70be71fb67378e30728e72e0c4e). -/
def _mm_max_epu8 (a b : __m128i) : __m128i :=
  zipBytes (fun x y => if x ≤ y then y else x) a b

/-- PSHUFB is local to each 128-bit half, even for a 256-bit register. -/
def shuffleBytes (a ctl : BitVec n) : BitVec n :=
  bytes n fun i =>
    let c := byte ctl i
    if c.msb then 0 else
      (a >>> (BitVec.ofNat n (128 * (i / 16)) +
        (c &&& 0x0f).zeroExtend n * 8)).extractLsb' 0 8

/-- VPSHUFB (XMM): byte shuffle with high-bit zeroing and low-nibble selection.
    [Clang documentation](https://clang.llvm.org/doxygen/tmmintrin_8h.html#ad598420994328403b84f9ae1a918e261). -/
def _mm_shuffle_epi8 (a ctl : __m128i) : __m128i := shuffleBytes a ctl

/-- VPSHUFB (YMM): two independent 128-bit byte shuffles, with high-bit zeroing.
    [Clang documentation](https://clang.llvm.org/doxygen/avx2intrin_8h.html#a60d6744087e4337ab69f06c33350810c). -/
def _mm256_shuffle_epi8 (a ctl : __m256i) : __m256i := shuffleBytes a ctl

/-- VPCMPEQB (YMM): byte equality, producing 0xff or zero per byte.
    [Clang documentation](https://clang.llvm.org/doxygen/avx2intrin_8h.html#a9481af7646c29f5cab1aa870ab0f198e). -/
def _mm256_cmpeq_epi8 (a b : __m256i) : __m256i :=
  zipBytes (fun x y => truthMask (x == y)) a b

/-- VPCMPGTB (YMM): signed byte greater-than, producing 0xff or zero per byte.
    [Clang documentation](https://clang.llvm.org/doxygen/avx2intrin_8h.html#a069381480a57b1d0a2a81d0e804f7711). -/
def _mm256_cmpgt_epi8 (a b : __m256i) : __m256i :=
  zipBytes (fun x y => truthMask (y.slt x)) a b

/-- VPBLENDVB (YMM): select each output byte using its mask byte's sign bit.
    [Clang documentation](https://clang.llvm.org/doxygen/avx2intrin_8h.html#a6311f7949c563dad42e1b423d3fc7b8a). -/
def _mm256_blendv_epi8 (a b mask : __m256i) : __m256i :=
  bytes 256 fun i => if (byte mask i).msb then byte b i else byte a i

/-- VPOR (YMM): bitwise OR.
    [Clang documentation](https://clang.llvm.org/doxygen/avx2intrin_8h.html#ac51e9c0b637d0f09591f73818c9736f1). -/
def _mm256_or_si256 (a b : __m256i) : __m256i := a ||| b

/-- VPAND (YMM): bitwise AND.
    [Clang documentation](https://clang.llvm.org/doxygen/avx2intrin_8h.html#aad42e1dec834b7dd756a66fcedef644c). -/
def _mm256_and_si256 (a b : __m256i) : __m256i := a &&& b

/-- VPMOVMSKB (YMM): byte i's high bit becomes scalar mask bit i.
    C++ returns a signed `int`; this model returns the same 32 bits as a
    `BitVec 32`, which is what the kernel's `static_cast<uint32_t>` yields.
    [Clang documentation](https://clang.llvm.org/doxygen/avx2intrin_8h.html#a03f9652a56c8022d5daee107527eb28c). -/
def _mm256_movemask_epi8 (a : __m256i) : BitVec 32 :=
  (List.range 32).foldl
    (fun acc i => acc ||| ((BitVec.ofBool (byte a i).msb).zeroExtend 32 <<< i)) 0

end Jumpdest.Avx2
