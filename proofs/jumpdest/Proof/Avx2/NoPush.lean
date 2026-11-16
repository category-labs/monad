import Proof.Avx2.Body

namespace Jumpdest.Avx2.Proof
open Jumpdest.Proof
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

/-- In a PUSH-free block the incoming skip is exhausted within 32 bytes.
    The unsigned lane comparison identifies exactly the remaining opcodes. -/
theorem no_push_circuit (op : __m256i) (skip : Byte) (entry : __m128i)
    (lane jumpdest : __m256i) (sixteen : __m128i)
    (hskip : skip ≤ 32) (hentry : entry = _mm_set1_epi8 (0x70 + skip))
    (h_lane : lane = _mm256_setr_epi8 #v[
    0x70, 0x71, 0x72, 0x73, 0x74, 0x75, 0x76, 0x77,
    0x78, 0x79, 0x7a, 0x7b, 0x7c, 0x7d, 0x7e, 0x7f,
    0x70, 0x71, 0x72, 0x73, 0x74, 0x75, 0x76, 0x77,
    0x78, 0x79, 0x7a, 0x7b, 0x7c, 0x7d, 0x7e, 0x7f])
    (h_jumpdest : jumpdest = _mm256_set1_epi8 EvmOpCode.JUMPDEST)
    (h_sixteen : sixteen = _mm_set1_epi8 16)
    (h_no_push : _mm256_movemask_epi8
      (_mm256_cmpgt_epi8 op (_mm256_set1_epi8 EvmOpCode.PUSH0)) == 0) :
    (_mm256_movemask_epi8 (_mm256_and_si256
      (_mm256_cmpeq_epi8 (_mm256_max_epu8
        (_mm256_set_m128i (_mm_sub_epi8 entry sixteen) entry) lane) lane)
      (_mm256_cmpeq_epi8 op jumpdest)), _mm_set1_epi8 0x70) =
      (streamMask op skip, _mm_set1_epi8 (0x70 + (stream (pairBytes op) skip).2)) := by
  change lane = (0x7f7e7d7c7b7a797877767574737271707f7e7d7c7b7a79787776757473727170 : BitVec 256) at h_lane
  change jumpdest = (0x5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b : BitVec 256) at h_jumpdest
  change sixteen = (0x10101010101010101010101010101010 : BitVec 128) at h_sixteen
  simp only [_mm256_max_epu8, _mm_set1_epi8, _mm256_set1_epi8,
    _mm_sub_epi8, _mm256_set_m128i, _mm256_cmpeq_epi8, _mm256_cmpgt_epi8,
    _mm256_and_si256, _mm256_movemask_epi8, zipBytes, bytes, truthMask, byte,
    streamMask, pairBytes, List.ofFn_succ, List.ofFn_zero, Fin.val_zero, Fin.val_succ,
    stream, skipNext, immediate, List.zipIdx_cons, List.zipIdx_nil,
    Nat.reduceDiv, Nat.reduceAdd, Nat.reduceMul,
    List.range_succ, List.range_zero, List.foldl_append, List.foldl_cons, List.foldl_nil,
    EvmOpCode.PUSH0, __m128i, __m256i, Byte, Prod.mk.injEq] at *
  bv_decide (config := { timeout := 120 })

end Jumpdest.Avx2.Proof
