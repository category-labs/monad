import Avx2Intrinsics

/-! Direct translation of find_jumpdests_avx2 in category/vm/interpreter/intercode.cpp.
    Equivalence.lean proves this implementation equivalent to Scalar.lean. -/
namespace Jumpdest.Avx2

def lift (nk pos lane : __m256i) : __m256i :=
  let q := _mm256_shuffle_epi8 nk pos
  let le := _mm256_cmpeq_epi8 (_mm256_max_epu8 q lane) lane
  _mm256_blendv_epi8 pos q le

def square (n : __m256i) : __m256i :=
  _mm256_max_epu8 (_mm256_shuffle_epi8 n n) n

/-- Return the updated bitmap. The caller supplies the original
    code_size and a code array with trailing zero padding (as in Intercode).
    The public wrapper below supplies both and initializes the bitmap. -/
def find_jumpdests_avx2 (code : Array Byte) (code_size : Nat) (bits : Bitmap) : Bitmap := Id.run do
  let mut bits := bits
  let npairs := (code_size + 31) / 32
  let len_floor := _mm256_set1_epi8 EvmOpCode.PUSH0
  let lane_bias := _mm256_setr_epi8 #v[
    0x12, 0x13, 0x14, 0x15, 0x16, 0x17, 0x18, 0x19,
    0x1a, 0x1b, 0x1c, 0x1d, 0x1e, 0x1f, 0x20, 0x21,
    0x12, 0x13, 0x14, 0x15, 0x16, 0x17, 0x18, 0x19,
    0x1a, 0x1b, 0x1c, 0x1d, 0x1e, 0x1f, 0x20, 0x21]
  let lane := _mm256_setr_epi8 #v[
    0x70, 0x71, 0x72, 0x73, 0x74, 0x75, 0x76, 0x77,
    0x78, 0x79, 0x7a, 0x7b, 0x7c, 0x7d, 0x7e, 0x7f,
    0x70, 0x71, 0x72, 0x73, 0x74, 0x75, 0x76, 0x77,
    0x78, 0x79, 0x7a, 0x7b, 0x7c, 0x7d, 0x7e, 0x7f]
  let jumpdest := _mm256_set1_epi8 EvmOpCode.JUMPDEST
  let minus_one := _mm256_set1_epi8 (-1)
  let sixteen := _mm_set1_epi8 16

  let mut entry := _mm_set1_epi8 0x70
  for b in [0:npairs] do
    let op := _mm256_loadu_si256 code (32 * b)
    let n0 := _mm256_add_epi8 (_mm256_max_epi8 op len_floor) lane_bias
    let n1 := square n0
    let n2 := square n1
    let n3 := square n2
    let n4 := square n3

    let n4_lo := _mm256_castsi256_si128 n4
    let n4_hi := _mm256_extracti128_si256 n4 1
    let entry_hi := _mm_sub_epi8
      (_mm_max_epu8 (_mm_shuffle_epi8 n4_lo entry) entry) sixteen
    let entry_next := _mm_sub_epi8
      (_mm_max_epu8 (_mm_shuffle_epi8 n4_hi entry_hi) entry_hi) sixteen

    let is_jumpdest := _mm256_cmpeq_epi8 op jumpdest
    let mask := if _mm256_movemask_epi8 is_jumpdest != 0 then
      let entries := _mm256_set_m128i entry_hi entry
      let pos := entries
      let pos := lift n3 pos lane
      let pos := lift n2 pos lane
      let pos := lift n1 pos lane
      let start := _mm256_or_si256
        (_mm256_cmpeq_epi8 pos lane)
        (_mm256_cmpeq_epi8 (_mm256_shuffle_epi8 n0 pos) lane)
      let in_block := _mm256_cmpgt_epi8 entries minus_one
      let jd := _mm256_and_si256
        (_mm256_and_si256 start in_block)
        is_jumpdest
      _mm256_movemask_epi8 jd
    else 0
    -- Corresponds to C++: std::memcpy(out + 4 * b, &mask, 4);
    bits := bits.store_u32_le (4 * b) mask
    entry := entry_next
  return bits

/-- Same Array Byte → Array Bool interface as the scalar computation. -/
def jumpdests_avx2 (code : Array Byte) : Bitmap :=
  let padded_code := pad code
  let initial := Array.replicate code.size false
  find_jumpdests_avx2 padded_code code.size initial

end Jumpdest.Avx2
