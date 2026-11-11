import Avx2
import Proof.Stream
import Proof.Avx2.Memory

namespace Jumpdest.Avx2.Proof
open Jumpdest.Proof
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

/-- Proof-only extraction of the literal loop body. `find_jumpdests_avx2_eq_pairs`
    checks that the extraction matches the implementation by definitional equality. -/
def pair (op : __m256i) (entry : __m128i) : BitVec 32 × __m128i :=
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
    (_mm256_cmpeq_epi8 op jumpdest)
  let mask := _mm256_movemask_epi8 jd
  (mask, entry_next)

theorem find_jumpdests_avx2_eq_pairs (code : Array Byte) (code_size : Nat) (bits : Bitmap) :
    find_jumpdests_avx2 code code_size bits = (Id.run do
      let mut bits := bits
      let mut entry := _mm_set1_epi8 0x70
      for b in [0:(code_size + 31) / 32] do
        let result := pair (_mm256_loadu_si256 code (32*b)) entry
        bits := store (8*(4*b)) result.1 (List.range 32) bits
        entry := result.2
      return bits) := by
  simp only [find_jumpdests_avx2, pair, store_u32_le_eq_store]

def pairBytes (op : __m256i) : List Byte := List.ofFn fun i : Fin 32 => byte op i.val

def streamMask (op : __m256i) (skip : Byte) : BitVec 32 :=
  ((stream (pairBytes op) skip).1.zipIdx).foldl
    (fun mask (b, i) => mask ||| ((BitVec.ofBool b).zeroExtend 32 <<< i)) 0

theorem pairBytes_length (op : __m256i) : (pairBytes op).length = 32 := by
  simp [pairBytes]

end Jumpdest.Avx2.Proof
