import Proof.Avx2.Body
namespace Jumpdest.Avx2.Proof
open Jumpdest.Proof
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

/-- Finite circuit lemma for the literal 32-byte loop body. Intermediate
    registers are quantified explicitly to preserve sharing during bit-blasting.
    `pair_eq_stream` supplies all defining equations by reflexivity. -/
theorem pair_circuit (op : __m256i) (skip : Byte) (entry : __m128i)
    (len_floor : __m256i)
    (lane_bias : __m256i)
    (lane : __m256i)
    (jumpdest : __m256i)
    (minus_one : __m256i)
    (sixteen : __m128i)
    (n0 : __m256i)
    (n1 : __m256i)
    (n2 : __m256i)
    (n3 : __m256i)
    (n4 : __m256i)
    (n4_lo : __m128i)
    (n4_hi : __m128i)
    (entry_hi : __m128i)
    (entry_next : __m128i)
    (entries : __m256i)
    (pos0 : __m256i)
    (pos1 : __m256i)
    (pos2 : __m256i)
    (pos : __m256i)
    (start : __m256i)
    (in_block : __m256i)
    (jd : __m256i)
    (mask : BitVec 32)
    (hskip : skip ≤ 32) (hentry : entry = _mm_set1_epi8 (0x70 + skip))
    (h_len_floor : len_floor = _mm256_set1_epi8 EvmOpCode.PUSH0)
    (h_lane_bias : lane_bias = _mm256_setr_epi8 #v[
    0x12, 0x13, 0x14, 0x15, 0x16, 0x17, 0x18, 0x19,
    0x1a, 0x1b, 0x1c, 0x1d, 0x1e, 0x1f, 0x20, 0x21,
    0x12, 0x13, 0x14, 0x15, 0x16, 0x17, 0x18, 0x19,
    0x1a, 0x1b, 0x1c, 0x1d, 0x1e, 0x1f, 0x20, 0x21])
    (h_lane : lane = _mm256_setr_epi8 #v[
    0x70, 0x71, 0x72, 0x73, 0x74, 0x75, 0x76, 0x77,
    0x78, 0x79, 0x7a, 0x7b, 0x7c, 0x7d, 0x7e, 0x7f,
    0x70, 0x71, 0x72, 0x73, 0x74, 0x75, 0x76, 0x77,
    0x78, 0x79, 0x7a, 0x7b, 0x7c, 0x7d, 0x7e, 0x7f])
    (h_jumpdest : jumpdest = _mm256_set1_epi8 EvmOpCode.JUMPDEST)
    (h_minus_one : minus_one = _mm256_set1_epi8 (-1))
    (h_sixteen : sixteen = _mm_set1_epi8 16)
    (h_n0 : n0 = _mm256_add_epi8 (_mm256_max_epi8 op len_floor) lane_bias)
    (h_n1 : n1 = square n0)
    (h_n2 : n2 = square n1)
    (h_n3 : n3 = square n2)
    (h_n4 : n4 = square n3)
    (h_n4_lo : n4_lo = _mm256_castsi256_si128 n4)
    (h_n4_hi : n4_hi = _mm256_extracti128_si256 n4 1)
    (h_entry_hi : entry_hi = _mm_sub_epi8
    (_mm_max_epu8 (_mm_shuffle_epi8 n4_lo entry) entry) sixteen)
    (h_entry_next : entry_next = _mm_sub_epi8
    (_mm_max_epu8 (_mm_shuffle_epi8 n4_hi entry_hi) entry_hi) sixteen)
    (h_entries : entries = _mm256_set_m128i entry_hi entry)
    (h_pos0 : pos0 = entries)
    (h_pos1 : pos1 = lift n3 pos0 lane)
    (h_pos2 : pos2 = lift n2 pos1 lane)
    (h_pos : pos = lift n1 pos2 lane)
    (h_start : start = _mm256_or_si256
    (_mm256_cmpeq_epi8 pos lane)
    (_mm256_cmpeq_epi8 (_mm256_shuffle_epi8 n0 pos) lane))
    (h_in_block : in_block = _mm256_cmpgt_epi8 entries minus_one)
    (h_jd : jd = _mm256_and_si256
    (_mm256_and_si256 start in_block)
    (_mm256_cmpeq_epi8 op jumpdest))
    (h_mask : mask = _mm256_movemask_epi8 jd)
    : (mask, entry_next) =
      (streamMask op skip, _mm_set1_epi8 (0x70 + (stream (pairBytes op) skip).2)) := by
  change len_floor = (0x5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f : BitVec 256) at h_len_floor
  change lane_bias = (0x21201f1e1d1c1b1a191817161514131221201f1e1d1c1b1a1918171615141312 : BitVec 256) at h_lane_bias
  change lane = (0x7f7e7d7c7b7a797877767574737271707f7e7d7c7b7a79787776757473727170 : BitVec 256) at h_lane
  change jumpdest = (0x5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b : BitVec 256) at h_jumpdest
  change minus_one = (0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff : BitVec 256) at h_minus_one
  change sixteen = (0x10101010101010101010101010101010 : BitVec 128) at h_sixteen
  simp only [lift, square, _mm256_add_epi8, _mm256_max_epi8,
    _mm256_max_epu8, _mm256_shuffle_epi8,
    _mm_set1_epi8, _mm256_castsi256_si128, _mm256_extracti128_si256,
    _mm_sub_epi8, _mm_max_epu8, _mm_shuffle_epi8, _mm256_set_m128i,
    _mm256_cmpeq_epi8, _mm256_cmpgt_epi8, _mm256_blendv_epi8,
    _mm256_or_si256, _mm256_and_si256, _mm256_movemask_epi8,
    shuffleBytes, zipBytes, bytes, truthMask, byte, streamMask, pairBytes,
    List.ofFn_succ, List.ofFn_zero, Fin.val_zero, Fin.val_succ,
    stream, skipNext, immediate, List.zipIdx_cons, List.zipIdx_nil,
    Nat.reduceDiv, Nat.reduceAdd, Nat.reduceMul,
    List.range_succ, List.range_zero, List.foldl_append, List.foldl_cons, List.foldl_nil,
    __m128i, __m256i, Byte, Prod.mk.injEq] at *
  bv_decide (config := { timeout := 120 })

end Jumpdest.Avx2.Proof
