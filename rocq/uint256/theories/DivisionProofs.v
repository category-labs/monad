(** * Long Division Proofs

    Correctness proofs for the long division model defined in Division.v.
*)

From Stdlib Require Import ZArith Lia List.
From Stdlib Require Import DoubleType.
From Uint256 Require Import Uint Primitives Words WordsLemmas Division.

Module MakeProofs (U64 : Uint64) (U128 : Uint128)
  (Import Bridge : UintWiden U64 U128).
Import U64.
Include Division.Make(U64)(U128)(Bridge).
Module WL := WordsLemmas.MakeProofs(U64).
Import WL.

Import ListNotations.
Open Scope Z_scope.

(** ** Local Helpers *)

Lemma Z_mul_le_contradiction : forall low M v s,
  M > 0 -> 0 <= low < M ->
  low + M * v >= M * s ->
  M * v <= M * (s - 1) -> False.
Proof. intros. nia. Qed.

Lemma Z_pow_split : forall s w,
  0 <= s <= w -> 2 ^ w = 2 ^ s * 2 ^ (w - s).
Proof.
  intros s w Hs. rewrite <- Z.pow_add_r by lia. f_equal. lia.
Qed.

Lemma shld64_zero : forall shift,
  to_Z (shld64 U64.zero U64.zero shift) = 0.
Proof.
  intros shift. unfold shld64.
  rewrite spec_or, spec_shl, spec_shr, spec_shr, spec_zero.
  assert (Hbw: base width <> 0) by (apply Z.pow_nonzero; lia).
  rewrite Z.shiftl_0_l, (Z.mod_0_l _ Hbw),
          Z.shiftr_0_l, (Z.mod_0_l _ Hbw),
          Z.lor_0_l, (Z.mod_0_l _ Hbw).
  reflexivity.
Qed.

(** If [lo < 2^k] and [hi] is aligned to [2^k] (no bits below [k]),
    their bits are disjoint. *)
Lemma Z_land_low_high : forall lo hi k,
  0 <= k ->
  0 <= lo < 2^k ->
  0 <= hi ->
  hi mod 2^k = 0 ->
  Z.land lo hi = 0.
Proof.
  intros lo hi k Hk Hlo Hhi Hmod.
  apply Z.bits_inj'. intros n Hn.
  rewrite Z.land_spec, Z.bits_0.
  destruct (Z.lt_ge_cases n k) as [Hlt | Hge].
  - (* n < k: bit n of hi is false because hi is aligned to 2^k *)
    rewrite Bool.andb_false_iff. right.
    assert (Hhi_eq: hi = Z.shiftl (hi / 2^k) k).
    { rewrite Z.shiftl_mul_pow2 by lia.
      pose proof (Z_div_mod_eq_full hi (2^k)). lia. }
    rewrite Hhi_eq. apply Z.shiftl_spec_low. lia.
  - (* n >= k: bit n of lo is false because lo < 2^k *)
    rewrite Bool.andb_false_iff. left.
    destruct (Z.eq_dec lo 0) as [->|Hnz].
    + rewrite Z.bits_0. reflexivity.
    + apply Z.bits_above_log2; [lia|].
      pose proof (proj1 (Z.log2_lt_pow2 lo k ltac:(lia)) ltac:(lia)). lia.
Qed.

(** Disjoint bits implies [lor = add]. *)
Corollary Z_lor_add_disjoint : forall lo hi k,
  0 <= k -> 0 <= lo < 2^k -> 0 <= hi ->
  hi mod 2^k = 0 ->
  Z.lor hi lo = hi + lo.
Proof.
  intros lo hi k Hk Hlo Hhi Hmod.
  pose proof (Z_land_low_high lo hi k Hk Hlo Hhi Hmod).
  rewrite Z.lor_comm. pose proof (Z.add_lor_land lo hi). lia.
Qed.

(** A product [a * 2^s] remains aligned to [2^s] after reduction mod [2^w]. *)
Lemma Z_mod_mul_pow2_aligned : forall a s w,
  0 <= s <= w ->
  (a * 2^s) mod 2^w mod 2^s = 0.
Proof.
  intros a s w Hsw.
  apply Z.mod_divide; [apply Z.pow_nonzero; lia|].
  pose proof (Z_pow_split s w Hsw) as Hw_eq.
  exists (a - a * 2^s / 2^w * 2^(w-s)).
  pose proof (Z_div_mod_eq_full (a * 2^s) (2^w)).
  lia.
Qed.

(** Euclidean-division complement: dividing by [2^(w-s)] is the same as
    multiplying by [2^s] then dividing by [2^w]. *)
Lemma Z_div_pow2_complement : forall x s w,
  0 <= x -> 0 <= s <= w ->
  x / 2^(w - s) = (x * 2^s) / 2^w.
Proof.
  intros x s w Hx Hs.
  rewrite (Z_pow_split s w Hs).
  rewrite <- Z.div_div
    by (first [apply Z.pow_nonzero; lia | apply Z.pow_pos_nonneg; lia]).
  rewrite Z_div_mult by (apply Z.lt_gt, Z.pow_pos_nonneg; lia).
  reflexivity.
Qed.

(** Right-shifting a value bounded by [2^w] keeps it below [2^w],
    so [mod 2^w] is a no-op. *)
Lemma Z_shiftr_mod_small : forall x w n,
  0 <= x < 2^w -> 0 <= n ->
  Z.shiftr x n mod 2^w = Z.shiftr x n.
Proof.
  intros x w n Hx Hn.
  apply Z.mod_small. split.
  - apply Z.shiftr_nonneg. lia.
  - rewrite Z.shiftr_div_pow2 by lia.
    apply Z.div_lt_upper_bound; [apply Z.pow_pos_nonneg; lia|].
    nia.
Qed.


(** Division distributes over [a + base * R] when the base is a
    power of 2 and the divisor divides the base. *)
Lemma Z_div_add_base_pow2 : forall a R s,
  0 <= a < 2 ^ (Z.pos width) -> 0 <= R -> 0 <= s <= Z.pos width ->
  (a + base width * R) / 2 ^ s = a / 2 ^ s + 2 ^ (Z.pos width - s) * R.
Proof.
  intros a R s Ha HR Hs.
  pose proof (Z_pow_split s (Z.pos width) ltac:(lia)) as Hpow.
  change (2 ^ Z.pos width) with (base width) in Hpow.
  rewrite Hpow.
  replace (a + 2 ^ s * 2 ^ (Z.pos width - s) * R)
    with (2 ^ (Z.pos width - s) * R * 2 ^ s + a) by ring.
  rewrite Z.div_add_l by (apply Z.pow_nonzero; lia).
  lia.
Qed.

(** ** Structural Properties *)

(** long_div_fold produces quotient with same length as input *)
Lemma long_div_fold_length : forall us v rem,
  length (ld_quot (long_div_fold us v rem)) = length us.
Proof.
  induction us as [|u rest IH]; intros v rem.
  - reflexivity.
  - unfold long_div_fold; fold long_div_fold.
    destruct (div rem u v) as [[q rm]|]; cbn [ld_quot length];
      rewrite IH; reflexivity.
Qed.

(** ** Correctness *)

(** Correctness of long_div_fold: processes MSW-first list.
    The invariant uses rev to convert from the big-endian quotient order
    produced by long_div_fold to the little-endian to_Z_words interpretation. *)
Lemma long_div_fold_correct : forall us v rem,
  to_Z v > 0 ->
  to_Z rem < to_Z v ->
  let r := long_div_fold us v rem in
  to_Z rem * modulus_words (length us) + to_Z_words (rev us) =
    to_Z_words (rev (ld_quot r)) * to_Z v + to_Z (ld_rem r).
Proof.
  induction us as [|u rest IH]; intros v rem Hv Hrem.
  - cbn [long_div_fold ld_quot ld_rem rev length to_Z_words].
    rewrite modulus_words_0.
    lia.
  - unfold long_div_fold; fold long_div_fold.
    pose proof (spec_div _ u _ Hv Hrem) as [q [rm [Hdiv_eq [Hdiv_val Hdiv_lt]]]].
    rewrite Hdiv_eq. cbn [ld_quot ld_rem].
    set (rec := long_div_fold rest v rm).
    pose proof (IH v rm Hv ltac:(lia)) as HIH.
    change (long_div_fold rest v rm) with rec in HIH.
    cbn in HIH.
    cbn [rev].
    rewrite !to_Z_words_app_single. rewrite !length_rev.
    cbn [length].
    rewrite modulus_words_succ.
    assert (Hlen: length (ld_quot rec) = length rest).
    { subst rec. apply long_div_fold_length. }
    rewrite Hlen.
    lia.
Qed.

(** Main correctness theorem for long_div *)
Theorem long_div_correct : forall us v,
  to_Z v > 0 ->
  let r := long_div us v in
  to_Z_words us = to_Z_words (ld_quot r) * to_Z v + to_Z (ld_rem r).
Proof.
  intros us v Hv. unfold long_div. cbn [ld_quot ld_rem].
  set (r := long_div_fold (rev us) v U64.zero).
  assert (Hrem: to_Z U64.zero < to_Z v) by (rewrite spec_zero; lia).
  pose proof (long_div_fold_correct (rev us) v U64.zero Hv Hrem) as Hfold.
  change (long_div_fold (rev us) v U64.zero) with r in Hfold.
  cbv zeta in Hfold. rewrite rev_involutive in Hfold.
  rewrite spec_zero, Z.mul_0_l, Z.add_0_l in Hfold.
  exact Hfold.
Qed.

(** ** Multi-Word Shift Correctness *)

(** [shld64] computes the high 64 bits of [(high || low) << shift].

    Given two 64-bit words and a shift amount [s] (0 < s < 64):

       high                  low
    [  63 ........... 0 | 63 ........... 0 ]

    After left-shifting the 128-bit concatenation by [s]:

    [  63 ........... 0 | 63 ........... 0 ]
     <---- result ----->
     |<-- 64-s -->|<-s->|
     | high<<s    | low>>(64-s)            |
     | (mod 2^64) |                        |

    Result = (high * 2^s) mod 2^64  +  low / 2^(64-s)
                  ^^^ kept bits            ^^^ overflow bits
                  (disjoint: low half aligned to 2^s,
                   high half bounded by 2^s)              *)
Lemma shld64_spec : forall high low shift,
  (shift < Pos.to_nat U64.width)%nat ->
  to_Z (shld64 high low shift) =
    (to_Z high * 2 ^ Z.of_nat shift) mod base width +
      to_Z low / 2 ^ (Z.pos width - Z.of_nat shift).
Proof.
  intros high low s Hs.
  pose proof (spec_to_Z high) as Hhigh.
  pose proof (spec_to_Z low) as Hlow.
  unfold shld64.
  rewrite spec_or, spec_shl.
  pose proof (spec_shr (shr low 1) (63 - s)) as Hshr_outer.
  pose proof (spec_shr low 1) as Hshr_inner.
  rewrite Hshr_inner in Hshr_outer.
  rewrite Hshr_outer.
  rewrite Z.shiftl_mul_pow2 by lia.
  unfold base in Hlow |- *.
  rewrite (Z_shiftr_mod_small (to_Z low) (Z.pos width) (Z.of_nat 1) Hlow ltac:(lia)).
  (* Collapse double shiftr *)
  rewrite Z.shiftr_shiftr by lia.
  rewrite width_is_64 in Hs.
  replace (Z.of_nat 1 + Z.of_nat (63 - s)) with (Z.pos 64 - Z.of_nat s) by lia.
  (* Outer shr mod is no-op *)
  rewrite (Z_shiftr_mod_small (to_Z low) (Z.pos width) (Z.pos 64 - Z.of_nat s) Hlow ltac:(lia)).
  rewrite Z.shiftr_div_pow2 by lia.
  replace (Z.pos width) with 64 by (rewrite width_is_64; reflexivity).
  (* Disjoint bits ⇒ lor = add *)
  set (a := (to_Z high * 2 ^ Z.of_nat s) mod 2^64).
  set (b := to_Z low / 2 ^ (64 - Z.of_nat s)).
  assert (Hlor: Z.lor a b = a + b).
  { apply (Z_lor_add_disjoint b a (Z.of_nat s)); [lia| | |].
    - unfold b. split.
      + apply Z.div_pos; [lia | apply Z.pow_pos_nonneg; lia].
      + apply Z.div_lt_upper_bound; [apply Z.pow_pos_nonneg; lia|].
        rewrite width_is_64 in Hlow.
        pose proof (Z_pow_split (Z.of_nat s) 64 ltac:(lia)). nia.
    - unfold a. pose proof (Z.mod_pos_bound (to_Z high * 2 ^ Z.of_nat s) (2^64)
                              ltac:(unfold base; apply Z.pow_pos_nonneg; lia)). lia.
    - unfold a. unfold base. apply Z_mod_mul_pow2_aligned. lia.
  }
  rewrite Hlor.
  (* Outer mod is no-op: a + b < base width *)
  apply Z.mod_small.
  assert (Ha_bound: 0 <= a < 2 ^ 64).
  { unfold a. apply Z.mod_pos_bound. apply Z.pow_pos_nonneg; lia. }
  assert (Hb_bound: 0 <= b < 2 ^ Z.of_nat s).
  { unfold b. split.
    - apply Z.div_pos; [lia | apply Z.pow_pos_nonneg; lia].
    - apply Z.div_lt_upper_bound; [apply Z.pow_pos_nonneg; lia|].
      rewrite width_is_64 in Hlow.
      pose proof (Z_pow_split (Z.of_nat s) 64 ltac:(lia)). nia.
  }
  split; [lia|].
  rewrite <- Hlor.
  destruct (Z.eq_dec (Z.lor a b) 0) as [->|Hlor_nz].
  + apply Z.pow_pos_nonneg; lia.
  + apply Z.log2_lt_pow2; [rewrite Hlor; lia|].
    rewrite Z.log2_lor by lia.
    apply Z.max_lub_lt.
    * destruct (Z.eq_dec a 0) as [->|]; [cbn; lia|].
      apply Z.log2_lt_pow2; lia.
    * destruct (Z.eq_dec b 0) as [->|]; [cbn; lia|].
      apply Z.log2_lt_pow2; [lia|].
      pose proof (Z.pow_le_mono_r 2 (Z.of_nat s) 64 ltac:(lia) ltac:(lia)). lia.
Qed.

(** Generalized invariant for [shift_left_words_aux]:
    the overflow bits from [prev] contribute to the result. *)
Lemma shift_left_words_aux_correct : forall ws prev shift,
  (shift < Pos.to_nat U64.width)%nat ->
  to_Z_words (shift_left_words_aux ws prev shift) =
    to_Z_words ws * 2 ^ Z.of_nat shift +
      to_Z prev / 2 ^ (Z.pos width - Z.of_nat shift).
Proof.
  induction ws as [|w rest IH]; intros prev s Hs.
  - cbn [shift_left_words_aux to_Z_words].
    rewrite shld64_spec by exact Hs.
    rewrite spec_zero, Z.mul_0_l, Zmod_0_l.
    lia.
  - cbn [shift_left_words_aux to_Z_words].
    rewrite shld64_spec by exact Hs.
    rewrite IH by exact Hs.
    ring_simplify.
    enough (H: (to_Z w * 2 ^ Z.of_nat s) mod base width +
               base width * (to_Z w / 2 ^ (Z.pos width - Z.of_nat s)) =
               2 ^ Z.of_nat s * to_Z w) by lia.
    rewrite (Z_div_pow2_complement (to_Z w) (Z.of_nat s) (Z.pos width))
      by (first [pose proof (spec_to_Z w); lia | lia]).
    pose proof (Z_div_mod_eq_full (to_Z w * 2 ^ Z.of_nat s) (base width)).
    unfold base in *.
    lia.
Qed.

(** Left-shift preserves value scaled by 2^shift.
    The result has length [length ws + 1] (overflow word appended). *)
Lemma shift_left_words_correct : forall ws shift,
  (shift < Pos.to_nat U64.width)%nat ->
  to_Z_words (shift_left_words ws shift) =
    to_Z_words ws * 2 ^ (Z.of_nat shift).
Proof.
  intros ws s Hs.
  unfold shift_left_words.
  rewrite shift_left_words_aux_correct by exact Hs.
  rewrite spec_zero.
  assert (0 / 2 ^ (Z.pos width - Z.of_nat s) = 0)
    by (apply Z.div_0_l; apply Z.pow_nonzero; lia).
  lia.
Qed.

(** ** Right-Shift Helpers *)

Lemma shrd64_zero : forall shift,
  to_Z (shrd64 U64.zero U64.zero shift) = 0.
Proof.
  intros shift. unfold shrd64.
  rewrite spec_or, spec_shr, spec_shl, spec_shl, spec_zero.
  assert (Hbw: base width <> 0) by (apply Z.pow_nonzero; lia).
  rewrite Z.shiftr_0_l, (Z.mod_0_l _ Hbw),
          Z.shiftl_0_l, (Z.mod_0_l _ Hbw),
          Z.lor_0_r, (Z.mod_0_l _ Hbw).
  reflexivity.
Qed.

(** [shrd64] computes the low 64 bits of [(high || low) >> shift].

    Given two 64-bit words and a shift amount [s] (0 < s < 64):

       high                  low
    [  63 ........... 0 | 63 ........... 0 ]

    After right-shifting the 128-bit concatenation by [s]:

    [  63 ........... 0 | 63 ........... 0 ]
                          <---- result ----->
                          |<-- 64-s -->|<-s->|
                          | high*2^(64-s)   | low/2^s  |
                          | (mod 2^64)      |          |

    Result = low / 2^s  +  (high * 2^(64-s)) mod 2^64
                ^^^ kept bits    ^^^ overflow bits
                (disjoint: high half aligned to 2^(64-s),
                 low half bounded by 2^(64-s))              *)
Lemma shrd64_spec : forall high low shift,
  (shift < Pos.to_nat U64.width)%nat ->
  to_Z (shrd64 high low shift) =
    to_Z low / 2 ^ Z.of_nat shift +
      (to_Z high * 2 ^ (Z.pos width - Z.of_nat shift)) mod base width.
Proof.
  intros high low s Hs.
  pose proof (spec_to_Z high) as Hhigh.
  pose proof (spec_to_Z low) as Hlow.
  unfold shrd64.
  rewrite spec_or, spec_shr.
  pose proof (spec_shl (shl high 1) (63 - s)) as Hshl_outer.
  pose proof (spec_shl high 1) as Hshl_inner.
  rewrite Hshl_inner in Hshl_outer.
  rewrite Hshl_outer.
  rewrite Z.shiftr_div_pow2 by lia.
  (* Remove the mod on the shr result — it's already in range *)
  assert (Hdiv_small: 0 <= to_Z low / 2 ^ Z.of_nat s < base width).
  { unfold base in Hlow |- *. split.
    - apply Z.div_pos; [lia | apply Z.pow_pos_nonneg; lia].
    - apply Z.div_lt_upper_bound.
      + apply Z.pow_pos_nonneg; lia.
      + pose proof (Z.pow_pos_nonneg 2 (Z.of_nat s) ltac:(lia) ltac:(lia)). nia. }
  rewrite (Z.mod_small _ _ Hdiv_small).
  (* Collapse double shl: shl (shl high 1) (63-s) = high * 2^(64-s) mod 2^64 *)
  rewrite Z.shiftl_mul_pow2 by lia.
  rewrite Z.shiftl_mul_pow2 by lia.
  rewrite width_is_64 in Hs.
  replace (Z.pos width) with 64 by (rewrite width_is_64; reflexivity).
  rewrite Z.mul_mod_idemp_l by (unfold base; apply Z.pow_nonzero; lia).
  replace (to_Z high * 2 ^ Z.of_nat 1 * 2 ^ Z.of_nat (63 - s))
    with (to_Z high * (2 ^ Z.of_nat 1 * 2 ^ Z.of_nat (63 - s))) by ring.
  replace (2 ^ Z.of_nat 1 * 2 ^ Z.of_nat (63 - s))
    with (2 ^ (64 - Z.of_nat s))
    by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
  (* Disjoint bits => lor = add *)
  set (a := to_Z low / 2 ^ Z.of_nat s).
  set (b := (to_Z high * 2 ^ (64 - Z.of_nat s)) mod base width).
  assert (Hlor: Z.lor a b = a + b).
  { rewrite Z.lor_comm. replace (a + b) with (b + a) by lia.
    apply (Z_lor_add_disjoint a b (64 - Z.of_nat s)); [lia| | |].
    - unfold a. split.
      + apply Z.div_pos; [lia | apply Z.pow_pos_nonneg; lia].
      + apply Z.div_lt_upper_bound; [apply Z.pow_pos_nonneg; lia|].
        unfold base in Hlow. rewrite width_is_64 in Hlow.
        pose proof (Z_pow_split (Z.of_nat s) 64 ltac:(lia)). nia.
    - unfold b. unfold base. rewrite width_is_64.
      pose proof (Z.mod_pos_bound (to_Z high * 2 ^ (64 - Z.of_nat s)) (2^64)
                    ltac:(apply Z.pow_pos_nonneg; lia)). lia.
    - unfold b. unfold base. rewrite width_is_64.
      apply Z_mod_mul_pow2_aligned. lia. }
  rewrite Hlor.
  (* Outer mod is no-op: a + b < base width *)
  apply Z.mod_small. unfold base. rewrite width_is_64.
  assert (Ha_bound: 0 <= a < 2 ^ (64 - Z.of_nat s)).
  { unfold a. split.
    - apply Z.div_pos; [lia | apply Z.pow_pos_nonneg; lia].
    - apply Z.div_lt_upper_bound; [apply Z.pow_pos_nonneg; lia|].
      unfold base in Hlow. rewrite width_is_64 in Hlow.
      pose proof (Z_pow_split (Z.of_nat s) 64 ltac:(lia)). nia. }
  assert (Hb_bound: 0 <= b < 2^64).
  { unfold b. unfold base. rewrite width_is_64.
    apply Z.mod_pos_bound. apply Z.pow_pos_nonneg; lia. }
  split; [lia|].
  rewrite <- Hlor.
  destruct (Z.eq_dec (Z.lor a b) 0) as [->|Hlor_nz].
  + apply Z.pow_pos_nonneg; lia.
  + apply Z.log2_lt_pow2; [rewrite Hlor; lia|].
    rewrite Z.log2_lor by lia.
    apply Z.max_lub_lt.
    * destruct (Z.eq_dec a 0) as [->|]; [cbn; lia|].
      apply Z.log2_lt_pow2; [lia|].
      pose proof (Z.pow_le_mono_r 2 (64 - Z.of_nat s) 64 ltac:(lia) ltac:(lia)). lia.
    * destruct (Z.eq_dec b 0) as [->|]; [cbn; lia|].
      apply Z.log2_lt_pow2; lia.
Qed.

(** Euclidean decomposition of [to_Z (hd zero rest) * 2^(w-s)] links
    the first word of [rest] to the full [to_Z_words rest]. *)
Lemma shift_right_hd_decomp : forall rest s,
  0 <= s <= Z.pos width ->
  (to_Z (hd zero rest) * 2 ^ (Z.pos width - s)) mod base width +
    base width * (to_Z_words rest / 2 ^ s) =
    2 ^ (Z.pos width - s) * to_Z_words rest.
Proof.
  intros rest s Hs.
  destruct rest as [|w' rest'].
  - cbn [hd to_Z_words].
    rewrite spec_zero, Z.mul_0_l, Zmod_0_l, Z.div_0_l, Z.mul_0_r, Z.mul_0_r.
    + reflexivity.
    + apply Z.pow_nonzero; lia.
  - cbn [hd to_Z_words].
    pose proof (spec_to_Z w') as Hw'.
    pose proof (to_Z_words_bound rest') as Hrest'.
    assert (Ha: 0 <= to_Z w' < 2 ^ Z.pos width) by (unfold base in Hw'; lia).
    rewrite (Z_div_add_base_pow2 (to_Z w') (to_Z_words rest') s Ha ltac:(lia) ltac:(lia)).
    pose proof (Z_div_pow2_complement (to_Z w') (Z.pos width - s) (Z.pos width)
                  ltac:(lia) ltac:(lia)) as Hcomp.
    replace (Z.pos width - (Z.pos width - s)) with s in Hcomp by lia.
    pose proof (Z_div_mod_eq_full (to_Z w' * 2 ^ (Z.pos width - s)) (base width)) as Heuc.
    unfold base in Heuc. rewrite <- Hcomp in Heuc. unfold base. nia.
Qed.

(** Right-shift divides value by 2^shift (truncating). *)
Lemma shift_right_words_correct : forall ws shift,
  (shift < Pos.to_nat U64.width)%nat ->
  to_Z_words (shift_right_words ws shift) =
    to_Z_words ws / 2 ^ (Z.of_nat shift).
Proof.
  induction ws as [|w rest IH]; intros s Hs.
  - cbn [shift_right_words to_Z_words].
    rewrite Z.div_0_l by (apply Z.pow_nonzero; lia). reflexivity.
  - cbn [shift_right_words to_Z_words].
    rewrite shrd64_spec by exact Hs.
    rewrite IH by exact Hs.
    pose proof (spec_to_Z w) as Hw.
    pose proof (to_Z_words_bound rest) as Hrest.
    assert (Ha: 0 <= to_Z w < 2 ^ Z.pos width) by (unfold base in Hw; lia).
    rewrite (Z_div_add_base_pow2 (to_Z w) (to_Z_words rest) (Z.of_nat s)
               Ha ltac:(lia) ltac:(lia)).
    (* Remains: hd decomposition — destruct rest *)
    rewrite <- Z.add_assoc.
    rewrite (shift_right_hd_decomp rest (Z.of_nat s)); lia.
Qed.

(** ** Shift-Left Structural Properties *)

Lemma shift_left_words_aux_length : forall ws prev shift,
  length (shift_left_words_aux ws prev shift) = S (length ws).
Proof.
  induction ws as [|w rest IH]; intros prev s.
  - reflexivity.
  - cbn [shift_left_words_aux length]. rewrite IH. reflexivity.
Qed.

Lemma shift_left_words_length : forall ws shift,
  length (shift_left_words ws shift) = S (length ws).
Proof.
  intros. unfold shift_left_words. apply shift_left_words_aux_length.
Qed.

(** The MSW (overflow word) of [shift_left_words ws s] is
    [shld64 0 (last ws) s], i.e., the top bits of the MSW of [ws]. *)
Lemma shift_left_words_aux_nth_msw : forall ws prev s,
  (length ws > 0)%nat ->
  nth (length ws) (shift_left_words_aux ws prev s) U64.zero =
    shld64 U64.zero (nth (length ws - 1) ws U64.zero) s.
Proof.
  induction ws as [|w rest IH]; intros prev s Hlen.
  - simpl in Hlen. lia.
  - destruct rest as [|w2 rest2].
    + simpl. reflexivity.
    + specialize (IH w s ltac:(simpl; lia)).
      change (shift_left_words_aux (w :: w2 :: rest2) prev s)
        with (shld64 w prev s :: shift_left_words_aux (w2 :: rest2) w s).
      change (length (w :: w2 :: rest2)) with (S (length (w2 :: rest2))).
      change (nth (S (length (w2 :: rest2)))
        (shld64 w prev s :: shift_left_words_aux (w2 :: rest2) w s) U64.zero)
        with (nth (length (w2 :: rest2))
          (shift_left_words_aux (w2 :: rest2) w s) U64.zero).
      replace (S (length (w2 :: rest2)) - 1)%nat
        with (length (w2 :: rest2)) by lia.
      simpl length. simpl nth.
      simpl length in IH. simpl nth in IH.
      replace (length rest2 - 0)%nat with (length rest2) in IH by lia.
      exact IH.
Qed.

Lemma shift_left_words_msw : forall ws s,
  (length ws > 0)%nat ->
  get_word (shift_left_words ws s) (length ws) =
    shld64 U64.zero (get_word ws (length ws - 1)) s.
Proof.
  intros ws s Hlen. unfold shift_left_words, get_word.
  apply shift_left_words_aux_nth_msw. exact Hlen.
Qed.

(** The overflow word of [shift_left_words ws s] is bounded by [2^s]. *)
Lemma shift_left_words_msw_bound : forall ws s,
  (s < Pos.to_nat U64.width)%nat ->
  (length ws > 0)%nat ->
  to_Z (get_word (shift_left_words ws s) (length ws)) < 2 ^ Z.of_nat s.
Proof.
  intros ws s Hs Hlen.
  rewrite shift_left_words_msw by exact Hlen.
  rewrite shld64_spec by exact Hs.
  rewrite spec_zero, Z.mul_0_l, Zmod_0_l. rewrite Z.add_0_l.
  pose proof (spec_to_Z (get_word ws (length ws - 1))) as Hw.
  unfold base in Hw.
  apply Z.div_lt_upper_bound; [apply Z.pow_pos_nonneg; lia|].
  rewrite <- Z.pow_add_r by lia.
  replace (Z.pos width - Z.of_nat s + Z.of_nat s) with (Z.pos width) by lia.
  lia.
Qed.

(** If the shifted value fits in [length ws] words, the overflow word is 0
    and [firstn (length ws)] preserves the value. *)
Lemma to_Z_words_firstn_shift_left : forall ws s,
  (s < Pos.to_nat U64.width)%nat ->
  to_Z_words ws * 2 ^ Z.of_nat s < modulus_words (length ws) ->
  to_Z_words (firstn (length ws) (shift_left_words ws s)) =
    to_Z_words ws * 2 ^ Z.of_nat s.
Proof.
  intros ws s Hs Hfit.
  pose proof (shift_left_words_correct ws s Hs) as Hval.
  pose proof (shift_left_words_length ws s) as Hlen.
  set (result := shift_left_words ws s) in *.
  assert (Hlen_le: (length ws <= length result)%nat) by lia.
  pose proof (to_Z_words_firstn_skipn result (length ws) Hlen_le) as Hsplit.
  rewrite Hval in Hsplit.
  pose proof (to_Z_words_bound (firstn (length ws) result)) as Hfirst_bound.
  rewrite firstn_length_le in Hfirst_bound by lia.
  pose proof (to_Z_words_bound (skipn (length ws) result)) as Hskip_bound.
  assert (Hskip_len: length (skipn (length ws) result) = 1%nat)
    by (rewrite length_skipn; lia).
  rewrite Hskip_len in Hskip_bound.
  rewrite modulus_words_succ, modulus_words_0 in Hskip_bound.
  (* skipn value must be 0 since full value < modulus_words (length ws) *)
  assert (to_Z_words (skipn (length ws) result) = 0) by nia.
  lia.
Qed.

(** ** Long Division Remainder Bound *)

Lemma long_div_fold_rem_bound : forall us v rem,
  to_Z v > 0 -> to_Z rem < to_Z v ->
  to_Z (ld_rem (long_div_fold us v rem)) < to_Z v.
Proof.
  induction us as [|u rest IH]; intros v rem Hv Hrem.
  - cbn [long_div_fold ld_rem]. exact Hrem.
  - unfold long_div_fold; fold long_div_fold.
    pose proof (spec_div _ u _ Hv Hrem) as [q [rm [Hdiv_eq [_ Hlt]]]].
    rewrite Hdiv_eq. cbn [ld_rem]. apply IH; [exact Hv | lia].
Qed.

Lemma long_div_rem_bound : forall us v,
  to_Z v > 0 ->
  to_Z (ld_rem (long_div us v)) < to_Z v.
Proof.
  intros us v Hv. unfold long_div. cbn [ld_rem].
  apply long_div_fold_rem_bound; [exact Hv|].
  rewrite spec_zero. lia.
Qed.

(** ** Countl_zero Properties *)

Lemma shr_zero_iff : forall x n,
  (n <= Pos.to_nat U64.width)%nat ->
  to_Z (U64.shr x n) = 0 <-> to_Z x < 2 ^ Z.of_nat n.
Proof.
  intros x n Hn.
  pose proof (spec_to_Z x) as Hx.
  rewrite spec_shr.
  rewrite Z.shiftr_div_pow2 by lia.
  assert (Hmod: to_Z x / 2 ^ Z.of_nat n mod base width =
                to_Z x / 2 ^ Z.of_nat n).
  { apply Z.mod_small. split.
    - apply Z.div_pos; [lia | apply Z.pow_pos_nonneg; lia].
    - apply Z.div_lt_upper_bound; [apply Z.pow_pos_nonneg; lia|].
      unfold base in Hx |- *.
      pose proof (Z.pow_pos_nonneg 2 (Z.of_nat n) ltac:(lia) ltac:(lia)). nia. }
  rewrite Hmod.
  split; intros H.
  - assert (Hpow: 2 ^ Z.of_nat n > 0) by (apply Z.lt_gt, Z.pow_pos_nonneg; lia).
    apply Z.div_small_iff in H; lia.
  - apply Z.div_small; lia.
Qed.

Lemma countl_zero_go_le : forall x pos,
  (countl_zero_go x pos <= pos)%nat.
Proof.
  intros x. induction pos as [|pos' IH].
  - cbn. lia.
  - cbn [countl_zero_go].
    destruct (U64.eqb (U64.shr x pos') U64.zero); [|lia].
    pose proof IH. lia.
Qed.

Lemma countl_zero_go_lt : forall x pos,
  to_Z x > 0 -> (pos > 0)%nat ->
  (countl_zero_go x pos < pos)%nat.
Proof.
  intros x. induction pos as [|pos' IH]; intros Hx Hpos.
  - lia.
  - cbn [countl_zero_go].
    destruct (U64.eqb (U64.shr x pos') U64.zero) eqn:Heq.
    + rewrite spec_eqb in Heq. apply Z.eqb_eq in Heq.
      destruct pos' as [|pos''].
      * exfalso.
        rewrite spec_shr in Heq. rewrite Z.shiftr_0_r in Heq.
        pose proof (spec_to_Z x).
        rewrite Z.mod_small in Heq by (unfold base in *; lia).
        rewrite spec_zero in Heq. lia.
      * pose proof (IH Hx ltac:(lia)). lia.
    + lia.
Qed.

Lemma countl_zero_bound : forall x,
  to_Z x > 0 ->
  (countl_zero x < Pos.to_nat U64.width)%nat.
Proof.
  intros x Hx. unfold countl_zero.
  apply countl_zero_go_lt; [exact Hx | lia].
Qed.

Lemma countl_zero_go_upper : forall x pos,
  to_Z x < 2 ^ Z.of_nat pos ->
  to_Z x < 2 ^ Z.of_nat (pos - countl_zero_go x pos).
Proof.
  intros x. induction pos as [|pos' IH]; intros Hbound.
  - cbn. exact Hbound.
  - cbn [countl_zero_go].
    destruct (U64.eqb (U64.shr x pos') U64.zero) eqn:Heq.
    + rewrite spec_eqb in Heq. apply Z.eqb_eq in Heq. rewrite spec_zero in Heq.
      pose proof (spec_to_Z x) as Hx.
      rewrite spec_shr in Heq. rewrite Z.shiftr_div_pow2 in Heq by lia.
      assert (Hsmall: 0 <= to_Z x / 2 ^ Z.of_nat pos' < base width).
      { split.
        - apply Z.div_pos; [lia | apply Z.pow_pos_nonneg; lia].
        - apply Z.div_lt_upper_bound.
          + apply Z.pow_pos_nonneg; lia.
          + unfold base in Hx |- *.
            pose proof (Z.pow_pos_nonneg 2 (Z.of_nat pos') ltac:(lia) ltac:(lia)). nia. }
      rewrite Z.mod_small in Heq by exact Hsmall.
      assert (Hlt: to_Z x < 2 ^ Z.of_nat pos').
      { assert (Hp: 2 ^ Z.of_nat pos' > 0) by (apply Z.lt_gt, Z.pow_pos_nonneg; lia).
        apply Z.div_small_iff in Heq; lia. }
      replace (S pos' - S (countl_zero_go x pos'))%nat
        with (pos' - countl_zero_go x pos')%nat by lia.
      apply IH. exact Hlt.
    + cbn [Nat.sub]. exact Hbound.
Qed.

Lemma countl_zero_upper : forall x,
  to_Z x < 2 ^ Z.of_nat (Pos.to_nat U64.width - countl_zero x).
Proof.
  intros x.
  unfold countl_zero. apply countl_zero_go_upper.
  pose proof (spec_to_Z x). unfold base in *. lia.
Qed.

Lemma countl_zero_shift_no_overflow : forall x,
  to_Z x > 0 ->
  to_Z x * 2 ^ Z.of_nat (countl_zero x) < base width.
Proof.
  intros x Hx.
  pose proof (countl_zero_upper x) as Hub.
  pose proof (countl_zero_bound x Hx) as Hcb.
  set (c := countl_zero x) in *.
  set (w := Pos.to_nat U64.width) in *.
  assert (Hpow: 2 ^ Z.of_nat (w - c) * 2 ^ Z.of_nat c = base width).
  { unfold base. rewrite <- Z.pow_add_r by lia. f_equal. lia. }
  nia.
Qed.

Lemma countl_zero_succ_shift_le : forall x,
  to_Z x > 0 ->
  (1 + to_Z x) * 2 ^ Z.of_nat (countl_zero x) <= base width.
Proof.
  intros x Hx.
  pose proof (countl_zero_upper x) as Hub.
  pose proof (countl_zero_bound x Hx) as Hcb.
  set (c := countl_zero x) in *.
  set (w := Pos.to_nat U64.width) in *.
  assert (Hpow: 2 ^ Z.of_nat (w - c) * 2 ^ Z.of_nat c = base width).
  { unfold base. rewrite <- Z.pow_add_r by lia. f_equal. lia. }
  nia.
Qed.

(** ** Count Significant Words Properties *)

Lemma skip_leading_zeros_le : forall rs,
  (skip_leading_zeros rs <= length rs)%nat.
Proof.
  induction rs as [|r rest IH].
  - cbn. lia.
  - cbn [skip_leading_zeros].
    destruct (U64.eqb r U64.zero); [|cbn; lia].
    cbn [length]. lia.
Qed.

Lemma count_significant_words_bound : forall ws,
  (count_significant_words ws <= length ws)%nat.
Proof.
  intros ws. unfold count_significant_words.
  pose proof (skip_leading_zeros_le (rev ws)).
  rewrite length_rev in H. exact H.
Qed.

(** Helper: elements in the leading-zero prefix (indices < length - slz) are zero. *)
Lemma skip_leading_zeros_zeros : forall rs i,
  (i < length rs - skip_leading_zeros rs)%nat ->
  to_Z (nth i rs U64.zero) = 0.
Proof.
  induction rs as [|r rest IH]; intros i Hi.
  - cbn in Hi. lia.
  - cbn [skip_leading_zeros] in Hi.
    destruct (U64.eqb r U64.zero) eqn:Heq.
    + rewrite spec_eqb in Heq. apply Z.eqb_eq in Heq. rewrite spec_zero in Heq.
      cbn [length] in Hi.
      destruct i as [|i'].
      * cbn. exact Heq.
      * cbn. apply IH. lia.
    + rewrite spec_eqb in Heq. apply Z.eqb_neq in Heq.
      cbn [length] in Hi. lia.
Qed.

(** Words beyond count_significant_words are zero *)
Lemma count_significant_words_trailing_zeros : forall ws i,
  (count_significant_words ws <= i < length ws)%nat ->
  to_Z (get_word ws i) = 0.
Proof.
  intros ws i Hi.
  unfold count_significant_words in Hi.
  unfold get_word.
  rewrite <- (rev_involutive ws) at 1.
  rewrite rev_nth by (rewrite length_rev; lia).
  rewrite length_rev.
  apply skip_leading_zeros_zeros.
  rewrite length_rev. lia.
Qed.

Lemma count_significant_words_preserves_value : forall ws,
  to_Z_words (firstn (count_significant_words ws) ws) = to_Z_words ws.
Proof.
  intros ws.
  apply to_Z_words_firstn_trailing_zeros.
  - apply count_significant_words_bound.
  - intros i Hi. apply count_significant_words_trailing_zeros. exact Hi.
Qed.

Lemma skip_leading_zeros_zero_value : forall rs,
  skip_leading_zeros rs = 0%nat ->
  forall i, (i < length rs)%nat -> to_Z (nth i rs U64.zero) = 0.
Proof.
  induction rs as [|r rest IH]; intros Hslz i Hi.
  - cbn in Hi. lia.
  - cbn [skip_leading_zeros] in Hslz.
    destruct (U64.eqb r U64.zero) eqn:Heq.
    + rewrite spec_eqb in Heq. apply Z.eqb_eq in Heq. rewrite spec_zero in Heq.
      destruct i as [|i'].
      * cbn. exact Heq.
      * cbn. apply IH; [exact Hslz | cbn in Hi; lia].
    + cbn [length] in Hslz. lia.
Qed.

Lemma count_significant_words_zero : forall ws,
  count_significant_words ws = 0%nat ->
  to_Z_words ws = 0.
Proof.
  intros ws Hcsw.
  apply to_Z_words_all_zero. intros i Hi.
  unfold get_word.
  unfold count_significant_words in Hcsw.
  rewrite <- (rev_involutive ws) at 1.
  rewrite rev_nth by (rewrite length_rev; lia).
  rewrite length_rev.
  apply skip_leading_zeros_zero_value; [exact Hcsw|].
  rewrite length_rev. lia.
Qed.

(** If csw > 0, the word at position csw-1 is nonzero *)
Lemma skip_leading_zeros_nonzero : forall rs,
  (skip_leading_zeros rs > 0)%nat ->
  to_Z (nth (length rs - skip_leading_zeros rs) rs U64.zero) > 0.
Proof.
  induction rs as [|r rest IH]; intros Hslz.
  - cbn in Hslz. lia.
  - cbn [skip_leading_zeros] in Hslz |- *.
    destruct (U64.eqb r U64.zero) eqn:Heq.
    + rewrite spec_eqb in Heq. apply Z.eqb_eq in Heq. rewrite spec_zero in Heq.
      cbn [length].
      replace (S (length rest) - skip_leading_zeros rest)%nat
        with (S (length rest - skip_leading_zeros rest))
        by (pose proof (skip_leading_zeros_le rest); lia).
      cbn [nth]. apply IH. exact Hslz.
    + rewrite spec_eqb in Heq. apply Z.eqb_neq in Heq. rewrite spec_zero in Heq.
      cbn [length].
      replace (S (length rest) - S (length rest))%nat with 0%nat by lia.
      cbn [nth]. pose proof (spec_to_Z r). lia.
Qed.

Lemma count_significant_words_msw_nonzero : forall ws,
  let n := count_significant_words ws in
  (n > 0)%nat ->
  to_Z (get_word ws (n - 1)) > 0.
Proof.
  intros ws n Hn.
  unfold n, count_significant_words in *.
  unfold get_word.
  set (rs := rev ws) in *.
  rewrite <- (rev_involutive ws) at 1.
  rewrite rev_nth.
  - change (rev ws) with rs.
    replace (length rs - S (skip_leading_zeros rs - 1))%nat
      with (length rs - skip_leading_zeros rs)%nat
      by (pose proof (skip_leading_zeros_le rs); lia).
    apply skip_leading_zeros_nonzero. exact Hn.
  - subst rs. pose proof (skip_leading_zeros_le (rev ws)). lia.
Qed.

Lemma count_significant_words_lower_bound : forall ws,
  let n := count_significant_words ws in
  (n > 0)%nat ->
  to_Z_words ws >= modulus_words (n - 1).
Proof.
  intros ws. cbv zeta. intros Hn.
  set (n := count_significant_words ws) in *.
  pose proof (count_significant_words_msw_nonzero ws Hn) as Hmsw.
  fold n in Hmsw.
  rewrite <- (count_significant_words_preserves_value ws). fold n.
  pose proof (count_significant_words_bound ws) as Hbn. fold n in Hbn.
  assert (Hlen: length (firstn n ws) = n) by (rewrite firstn_length_le; lia).
  rewrite (to_Z_words_firstn_skipn (firstn n ws) (n - 1)) by (rewrite Hlen; lia).
  pose proof (to_Z_words_bound (firstn (n-1) (firstn n ws))) as Hfb.
  assert (Hskip: to_Z_words (skipn (n-1) (firstn n ws)) >= 1).
  { rewrite skipn_firstn_comm. replace (n - (n-1))%nat with 1%nat by lia.
    destruct (skipn (n-1) ws) as [|w rest] eqn:Hsk.
    - exfalso. assert (length (skipn (n-1) ws) = 0%nat) by (rewrite Hsk; reflexivity).
      rewrite length_skipn in H. lia.
    - cbn [firstn to_Z_words].
      assert (Hw: w = get_word ws (n-1)).
      { unfold get_word. symmetry.
        change w with (nth 0 (w :: rest) U64.zero).
        rewrite <- Hsk. rewrite nth_skipn. f_equal. lia. }
      rewrite Hw. pose proof (spec_to_Z (get_word ws (n-1))). lia. }
  pose proof (modulus_words_pos (n-1)). nia.
Qed.

(** ** Long Division Quotient Length *)

Lemma long_div_quot_length : forall us v,
  length (ld_quot (long_div us v)) = length us.
Proof.
  intros us v. unfold long_div. cbn [ld_quot].
  rewrite length_rev, long_div_fold_length, length_rev.
  reflexivity.
Qed.

(** ** Segment Infrastructure *)

Lemma get_segment_length : forall ws start len,
  (start + len <= length ws)%nat ->
  length (get_segment ws start len) = len.
Proof.
  intros. unfold get_segment.
  rewrite firstn_length_le by (rewrite length_skipn; lia). reflexivity.
Qed.

Lemma get_word_get_segment : forall ws start len j,
  (j < len)%nat -> (start + len <= length ws)%nat ->
  get_word (get_segment ws start len) j = get_word ws (start + j).
Proof.
  intros ws start len j Hj Hlen.
  unfold get_word, get_segment.
  rewrite nth_firstn. replace ((j <? len)%nat) with true
    by (symmetry; apply Nat.ltb_lt; lia).
  rewrite nth_skipn. reflexivity.
Qed.

Lemma set_segment_length : forall ws start seg,
  (start + length seg <= length ws)%nat ->
  length (set_segment ws start seg) = length ws.
Proof.
  intros ws. induction ws as [|w rest IH]; intros start seg Hlen.
  - destruct start; simpl in Hlen; [destruct seg; simpl in *; lia | lia].
  - destruct start as [|start'].
    + simpl. rewrite length_app, length_skipn. simpl length in *. lia.
    + simpl set_segment. simpl length. f_equal. apply IH. simpl in Hlen. lia.
Qed.

Lemma get_word_set_segment_inside : forall ws start seg j,
  (start <= j)%nat -> (j < start + length seg)%nat ->
  (start + length seg <= length ws)%nat ->
  get_word (set_segment ws start seg) j = get_word seg (j - start).
Proof.
  intros ws. induction ws as [|w rest IH]; intros start seg j Hlo Hhi Hlen.
  - simpl in Hlen. lia.
  - destruct start as [|start'].
    + simpl. replace (j - 0)%nat with j by lia.
      unfold get_word. rewrite app_nth1 by lia. reflexivity.
    + destruct j as [|j']; [lia|].
      simpl set_segment. cbn [get_word nth].
      replace (S j' - S start')%nat with (j' - start')%nat by lia.
      apply IH; simpl in *; lia.
Qed.

Lemma get_word_set_segment_outside : forall ws start seg j,
  (j < start \/ start + length seg <= j)%nat ->
  (start + length seg <= length ws)%nat ->
  get_word (set_segment ws start seg) j = get_word ws j.
Proof.
  intros ws. induction ws as [|w rest IH]; intros start seg j Hout Hlen.
  - destruct start; simpl in Hlen; destruct seg; simpl in *; try lia; reflexivity.
  - destruct start as [|start'].
    + simpl. destruct Hout as [Hlt|Hge]; [lia|].
      unfold get_word. rewrite app_nth2 by lia.
      rewrite nth_skipn. f_equal. lia.
    + destruct j as [|j'].
      * reflexivity.
      * simpl set_segment. cbn [get_word nth]. apply IH; simpl in *; [lia | lia].
Qed.

Lemma get_segment_set_segment_same : forall ws start seg,
  (start + length seg <= length ws)%nat ->
  get_segment (set_segment ws start seg) start (length seg) = seg.
Proof.
  intros ws start seg Hlen.
  apply nth_ext with (d := U64.zero) (d' := U64.zero).
  - rewrite get_segment_length by (rewrite set_segment_length by lia; lia).
    reflexivity.
  - intros n Hn.
    rewrite get_segment_length in Hn
      by (rewrite set_segment_length by lia; lia).
    change (nth n (get_segment (set_segment ws start seg) start (length seg))
      U64.zero) with
      (get_word (get_segment (set_segment ws start seg) start (length seg)) n).
    rewrite get_word_get_segment
      by (first [exact Hn | rewrite set_segment_length by lia; lia]).
    rewrite get_word_set_segment_inside by lia.
    unfold get_word. f_equal. lia.
Qed.

(** ** Segment Value Decomposition *)

Lemma to_Z_words_firstn_segment : forall ws start len,
  (start + len <= length ws)%nat ->
  to_Z_words (firstn (start + len) ws) =
    to_Z_words (firstn start ws) +
    modulus_words start * to_Z_words (get_segment ws start len).
Proof.
  intros ws start len Hlen.
  rewrite (to_Z_words_firstn_skipn (firstn (start + len) ws) start).
  2: { rewrite firstn_length_le by lia. lia. }
  f_equal.
  { f_equal. rewrite firstn_firstn.
    replace (Nat.min start (start + len)) with start by lia. reflexivity. }
  { f_equal. unfold get_segment. rewrite skipn_firstn_comm.
    replace (start + len - start)%nat with len by lia. reflexivity. }
Qed.

Lemma remainder_msw_le : forall r v,
  length r = length v ->
  (length r > 0)%nat ->
  0 <= to_Z_words r < to_Z_words v ->
  to_Z (get_word r (length r - 1)) <= to_Z (get_word v (length v - 1)).
Proof.
  intros r v Hlen Hpos [Hrnn Hrlt].
  set (k := (length r - 1)%nat).
  destruct (Z.le_gt_cases (to_Z (get_word r k)) (to_Z (get_word v k))).
  { replace (length v - 1)%nat with k by (unfold k; lia). exact H. }
  exfalso.
  rewrite (to_Z_words_firstn_skipn r k) in Hrlt by lia.
  rewrite (to_Z_words_firstn_skipn v k) in Hrlt by (rewrite Hlen in *; lia).
  pose proof (to_Z_words_bound (firstn k v)) as Hlow_v.
  rewrite firstn_length_le in Hlow_v by lia.
  (* skipn k r and skipn k v each have exactly 1 element *)
  assert (Hsr: to_Z_words (skipn k r) = to_Z (get_word r k)).
  { destruct (skipn k r) as [|w rest] eqn:Hsk.
    - exfalso. assert (length (skipn k r) = 0%nat) by (rewrite Hsk; reflexivity).
      rewrite length_skipn in H0. lia.
    - assert (rest = [])
        by (assert (length (w :: rest) = 1%nat)
              by (rewrite <- Hsk, length_skipn; unfold k; lia);
            destruct rest; [reflexivity | simpl in *; lia]).
      subst rest. cbn [to_Z_words].
      assert (w = get_word r k)
        by (unfold get_word; symmetry;
            change w with (nth 0 (w :: []) U64.zero);
            rewrite <- Hsk, nth_skipn; f_equal; unfold k; lia).
      rewrite H0. lia. }
  assert (Hkv: (k < length v)%nat) by (unfold k; lia).
  assert (Hsv: to_Z_words (skipn k v) = to_Z (get_word v k)).
  { destruct (skipn k v) as [|w rest] eqn:Hsk.
    - exfalso. assert (length (skipn k v) = 0%nat) by (rewrite Hsk; reflexivity).
      rewrite length_skipn in *. lia.
    - assert (rest = [])
        by (assert (length (w :: rest) = 1%nat)
              by (rewrite <- Hsk, length_skipn; unfold k; lia);
            destruct rest; [reflexivity | simpl in *; lia]).
      subst rest. cbn [to_Z_words].
      assert (w = get_word v k)
        by (unfold get_word; symmetry;
            change w with (nth 0 (w :: []) U64.zero);
            rewrite <- Hsk, nth_skipn; f_equal; unfold k; lia).
      rewrite H0. lia. }
  rewrite Hsr, Hsv in Hrlt.
  pose proof (modulus_words_pos k).
  pose proof (to_Z_words_bound (firstn k r)) as Hlow_r.
  rewrite firstn_length_le in Hlow_r by lia.
  nia.
Qed.

(** ** Knuth Subtract-and-Correct *)

(** knuth_sub_loop computes [u_seg - q_hat * v] with borrow propagation.
    The mathematical value of the segment decreases by [q_hat * v_val],
    modulo the segment width, with the borrow [k] tracking the overflow. *)
Lemma knuth_sub_loop_correct : forall u_seg q_hat vs j k,
  length u_seg = (j + length vs)%nat ->
  let '(u', k') := knuth_sub_loop u_seg q_hat vs j k in
  to_Z_words u' + U128.to_Z k' * modulus_words (j + length vs) =
    to_Z_words u_seg - (U128.to_Z q_hat * to_Z_words vs - U128.to_Z k) *
      base width ^ (Z.of_nat j).
Proof.
Admitted.

(** knuth_addback_loop computes [u_seg + v] with carry propagation.
    Used when the trial quotient overestimated by 1. *)
Lemma knuth_addback_loop_correct : forall u_seg vs j k,
  length u_seg = (j + length vs)%nat ->
  let '(u', k') := knuth_addback_loop u_seg vs j k in
  to_Z_words u' + U128.to_Z k' * modulus_words (j + length vs) =
    to_Z_words u_seg + (to_Z_words vs + U128.to_Z k)
      * base width ^ (Z.of_nat j).
Proof. Admitted.

(** knuth_div_subtract: one full subtract-and-correct step.
    Returns [(u_after, q_final)] where:
    - [u_after] is the updated segment
    - [q_final] is the corrected quotient digit
    The key invariant: [u_orig = q_final * v + u_after] over the segment. *)
Lemma knuth_div_subtract_correct : forall u_seg q_hat v n,
  length u_seg = (n + 1)%nat -> length v = n ->
  to_Z_words v > 0 ->
  let '(u_after, q_final) := knuth_div_subtract u_seg q_hat v n in
  to_Z_words u_seg =
    to_Z q_final * to_Z_words v + to_Z_words (firstn n u_after)
  /\ 0 <= to_Z_words (firstn n u_after) < to_Z_words v
  /\ length u_after = (n + 1)%nat
  /\ get_word u_after n = U64.zero.
Proof. Admitted.

(** ** Knuth Division — Single Step and Loop *)

(** knuth_div_step: one iteration combining estimate + subtract + correct. *)
Lemma knuth_div_step_correct : forall u v i n,
  length v = n -> (n > 1)%nat ->
  (i + n < length u)%nat ->
  to_Z_words v > 0 ->
  to_Z (get_word u (i + n)) <= to_Z (get_word v (n - 1)) ->
  let '(u', q_i) := knuth_div_step u v i n in
  (* Euclidean decomposition of the segment *)
  to_Z_words (get_segment u i (n + 1)) =
    to_Z q_i * to_Z_words v + to_Z_words (firstn n (get_segment u' i (n + 1)))
  /\ 0 <= to_Z_words (firstn n (get_segment u' i (n + 1))) < to_Z_words v
  (* Length preserved *)
  /\ length u' = length u
  (* Words outside [i, i+n] unchanged *)
  /\ (forall j, (j < i \/ i + n < j)%nat -> (j < length u)%nat ->
        get_word u' j = get_word u j)
  (* MSW of modified segment is zero — remainder fits in n words *)
  /\ get_word u' (i + n) = U64.zero.
Proof.
  intros u v i n Hlv Hn Hi Hvpos Hmsw.
  unfold knuth_div_step.
  set (q_hat := knuth_div_estimate (get_word u (i + n)) (get_word u (i + n - 1))
    (get_word u (i + n - 2)) (get_word v (n - 1)) (get_word v (n - 2))).
  change (MakeProofs.get_word) with get_word.
  change (MakeProofs.get_segment) with get_segment.
  fold q_hat.
  destruct (U128.eqb q_hat U128.zero) eqn:Hq;
    [| fold (get_segment u i (n + 1))].
  - (* Case q_hat = 0 *)
    set (u_hi := get_word u (i + n)) in *.
    set (u_mid := get_word u (i + n - 1)) in *.
    set (v_hi := get_word v (n - 1)) in *.
    unfold q_hat, knuth_div_estimate in Hq.
    destruct (U64.eqb u_hi v_hi) eqn:Heq_hi.
    + (* u_hi = v_hi: widen u64_max_val ≠ 0 — contradiction *)
      exfalso.
      rewrite U128.spec_eqb in Hq. apply Z.eqb_eq in Hq.
      rewrite U128.spec_zero in Hq.
      pose proof (spec_widen u64_max_val) as Hw. rewrite Hw in Hq.
      unfold u64_max_val in Hq.
      pose proof (spec_to_Z (U64.sub U64.zero U64.one)) as [Hnn Hlt].
      rewrite spec_sub, spec_zero, spec_one in Hq.
      assert (Hb: base width > 1) by (unfold base; rewrite width_is_64; lia).
      apply Z.mod_divide in Hq; [| unfold base; apply Z.pow_nonzero; lia].
      destruct Hq as [k Hk].
      destruct (Z.eq_dec k 0); [lia|].
      assert (Z.abs k >= 1) by lia.
      assert (Z.abs (k * base width) >= base width).
      { rewrite Z.abs_mul.
        assert (Z.abs (base width) = base width) by (apply Z.abs_eq; lia).
        nia. }
      lia.
    + (* u_hi ≠ v_hi *)
      rewrite spec_eqb in Heq_hi. apply Z.eqb_neq in Heq_hi.
      assert (Hu_lt_v: to_Z u_hi < to_Z v_hi)
        by (clear - Hmsw Heq_hi; lia).
      assert (Hv_hi_pos: to_Z v_hi > 0)
        by (clear - Hu_lt_v; pose proof (spec_to_Z u_hi); lia).
      pose proof (spec_div u_hi u_mid v_hi Hv_hi_pos Hu_lt_v)
        as [q0 [r0 [Hdiv_eq [Hdiv_val Hdiv_lt]]]].
      rewrite Hdiv_eq in Hq.
      destruct (U64.eqb q0 U64.zero) eqn:Hq0.
      * (* q0 = 0: derive u_hi = 0, u_mid < v_hi *)
        rewrite spec_eqb in Hq0. rewrite spec_zero in Hq0.
        apply Z.eqb_eq in Hq0.
        rewrite Hq0, Z.mul_0_l, Z.add_0_l in Hdiv_val.
        pose proof (spec_to_Z u_hi) as [Hu_nn Hu_lt_base].
        pose proof (spec_to_Z u_mid) as [Humid_nn _].
        assert (Hu_hi_zero: to_Z u_hi = 0).
        { destruct (Z.eq_dec (to_Z u_hi) 0) as [|Hnz]; [exact e|exfalso].
          assert (base width * 1 <= base width * to_Z u_hi).
          { apply Z.mul_le_mono_nonneg_l;
              [unfold base; apply Z.pow_nonneg; lia | lia]. }
          pose proof (spec_to_Z v_hi). unfold base in *. lia. }
        assert (Humid_lt: to_Z u_mid < to_Z v_hi) by lia.
        assert (Hu_hi_eq: u_hi = U64.zero)
          by (apply spec_to_Z_inj; rewrite spec_zero; exact Hu_hi_zero).
        rewrite spec_zero. rewrite Z.mul_0_l, Z.add_0_l.
        assert (Hseg_msw: to_Z (get_word (get_segment u i (n + 1)) n) = 0).
        { rewrite get_word_get_segment by lia.
          unfold u_hi in Hu_hi_zero. exact Hu_hi_zero. }
        split; [|split; [|split; [reflexivity|split; [auto|exact Hu_hi_eq]]]].
        { (* Euclidean: segment = firstn n segment since MSW = 0 *)
          rewrite (to_Z_words_firstn_skipn (get_segment u i (n + 1)) n)
            by (try rewrite Hseg_len; try (rewrite get_segment_length by lia); lia).
          (* skipn n seg has 1 element = 0, so its value is 0 *)
          assert (Hskip0: to_Z_words (skipn n (get_segment u i (n + 1))) = 0).
          { destruct (skipn n (get_segment u i (n + 1))) as [|w rest] eqn:Hsk.
            - reflexivity.
            - assert (rest = [])
                by (assert (length (w :: rest) = 1%nat)
                      by (rewrite <- Hsk, length_skipn, get_segment_length by lia; lia);
                    destruct rest; [reflexivity | simpl in *; lia]).
              subst rest. cbn [to_Z_words].
              assert (w = get_word (get_segment u i (n + 1)) n).
              { unfold get_word. change w with (nth 0 (w :: []) U64.zero).
                rewrite <- Hsk, nth_skipn. f_equal. lia. }
              rewrite H. rewrite Hseg_msw. lia. }
          rewrite Hskip0. lia. }
        { (* Remainder bound *)
          split; [apply to_Z_words_bound|].
          (* Decompose firstn n seg at position n-1 *)
          set (seg := get_segment u i (n + 1)).
          pose proof (to_Z_words_bound (firstn (n - 1) (firstn n seg))) as Hlow_bound.
          rewrite firstn_firstn, Nat.min_l in Hlow_bound by lia.
          assert (Hseg_len: length seg = (n + 1)%nat)
            by (unfold seg; try rewrite Hseg_len; try (rewrite get_segment_length by lia); lia).
          rewrite firstn_length_le in Hlow_bound by lia.
          rewrite (to_Z_words_firstn_skipn (firstn n seg) (n - 1))
            by (rewrite firstn_length_le by (try rewrite Hseg_len; try (rewrite get_segment_length by lia); lia); lia).
          (* The (n-1)-th word of seg is u_mid *)
          assert (Hseg_mid: get_word seg (n - 1) = u_mid).
          { unfold seg. rewrite get_word_get_segment by lia.
            unfold u_mid. f_equal. lia. }
          (* skipn (n-1) (firstn n seg) has 1 element = seg[n-1] = u_mid *)
          assert (Hskip_val: to_Z_words (skipn (n - 1) (firstn n seg)) = to_Z u_mid).
          { destruct (skipn (n - 1) (firstn n seg)) as [|w rest] eqn:Hsk.
            - exfalso. assert (length (skipn (n-1) (firstn n seg)) = 0%nat)
                by (rewrite Hsk; reflexivity).
              rewrite length_skipn, firstn_length_le in H
                by (try rewrite Hseg_len; try (rewrite get_segment_length by lia); lia). lia.
            - assert (rest = [])
                by (assert (length (w :: rest) = 1%nat)
                      by (rewrite <- Hsk, length_skipn, firstn_length_le
                            by (try rewrite Hseg_len; try (rewrite get_segment_length by lia); lia); lia);
                    destruct rest; [reflexivity | simpl in *; lia]).
              subst rest. cbn [to_Z_words].
              assert (w = get_word seg (n - 1)).
              { unfold get_word. change w with (nth 0 (w :: []) U64.zero).
                rewrite <- Hsk, nth_skipn.
                rewrite nth_firstn.
                replace ((n - 1 + 0 <? n)%nat) with true
                  by (symmetry; apply Nat.ltb_lt; lia).
                f_equal. lia. }
              rewrite H, Hseg_mid. lia. }
          rewrite Hskip_val.
          rewrite firstn_firstn, Nat.min_l by lia.
          (* Now: low + modulus(n-1) * u_mid < modulus(n-1) * (1 + u_mid) <= modulus(n-1) * v_hi *)
          pose proof (modulus_words_pos (n - 1)).
          assert (Hv_decomp: to_Z_words v >= modulus_words (n - 1) * to_Z v_hi).
          { rewrite (to_Z_words_firstn_skipn v (n - 1)) by lia.
            pose proof (to_Z_words_bound (firstn (n - 1) v)).
            rewrite firstn_length_le in H0 by lia.
            (* skipn (n-1) v has >= 1 element, first is v[n-1] = v_hi *)
            assert (to_Z_words (skipn (n - 1) v) >= to_Z v_hi).
            { destruct (skipn (n - 1) v) as [|w rest] eqn:Hsk.
              - exfalso. assert (length (skipn (n-1) v) = 0%nat)
                  by (rewrite Hsk; reflexivity).
                rewrite length_skipn in H1. lia.
              - cbn [to_Z_words]. pose proof (spec_to_Z w).
                pose proof (to_Z_words_bound rest).
                assert (Hwv: w = get_word v (n - 1)).
                { unfold get_word. change w with (nth 0 (w :: rest) U64.zero).
                  rewrite <- Hsk, nth_skipn. f_equal. lia. }
                unfold v_hi. rewrite <- Hwv.
                pose proof (modulus_words_pos (length rest)). nia. }
            nia. }
          assert (modulus_words (n - 1) * (1 + to_Z u_mid) <=
            modulus_words (n - 1) * to_Z v_hi).
          { apply Z.mul_le_mono_nonneg_l; lia. }
          lia. }
      * (* q0 ≠ 0 but estimate = 0 — contradiction *)
        exfalso.
        rewrite spec_eqb in Hq0. apply Z.eqb_neq in Hq0. rewrite spec_zero in Hq0.
        rewrite U128.spec_eqb in Hq. apply Z.eqb_eq in Hq. rewrite U128.spec_zero in Hq.
        destruct (U128.gtb _ _).
        { (* widen q0 - 1 = 0 implies widen q0 = 1 implies q0 = 1, nonzero *)
          admit. }
        { (* widen q0 = 0 implies q0 = 0 — contradiction *)
          pose proof (spec_widen q0).
          pose proof (spec_to_Z q0).
          rewrite Hq in H. lia. }
  - (* Case q_hat ≠ 0 *)
    pose proof (knuth_div_subtract_correct (get_segment u i (n + 1)) q_hat v n
      ltac:(try rewrite Hseg_len; try (rewrite get_segment_length by lia); lia) Hlv Hvpos) as Hsub.
    destruct (knuth_div_subtract (get_segment u i (n + 1)) q_hat v n)
      as [new_seg final_q].
    destruct Hsub as [Heuclid [Hrem [Hlen_seg Hmsw_seg]]].
    replace (n + 1)%nat with (length new_seg) in |- * by lia.
    rewrite (get_segment_set_segment_same u i new_seg ltac:(lia)).
    replace (length new_seg) with (n + 1)%nat in |- * by lia.
    split; [exact Heuclid|].
    split; [exact Hrem|].
    split; [apply set_segment_length; lia|].
    split.
    + intros j Hout Hj. apply get_word_set_segment_outside; lia.
    + rewrite get_word_set_segment_inside by lia.
      replace (i + n - i)%nat with n by lia. exact Hmsw_seg.
Admitted.

(** knuth_div_loop: the outer loop iterating from [m-n] down to [0].
    Invariant: the accumulated value [firstn (ci+n+1) u + quot * v] is
    conserved across iterations. *)
Lemma knuth_div_loop_correct : forall u v quot n fuel current_i,
  length v = n -> (n > 1)%nat ->
  to_Z_words v > 0 ->
  (current_i + n < length u)%nat ->
  (current_i < length quot)%nat ->
  fuel = S current_i ->
  to_Z (get_word u (current_i + n)) <= to_Z (get_word v (n - 1)) ->
  (forall j, (j <= current_i)%nat -> to_Z (get_word quot j) = 0) ->
  let '(u_after, quot_final) := knuth_div_loop u v quot n fuel current_i in
  (* Value conservation *)
  to_Z_words (firstn (current_i + n + 1) u) + to_Z_words quot * to_Z_words v =
    to_Z_words quot_final * to_Z_words v + to_Z_words (firstn n u_after)
  (* Remainder bound *)
  /\ 0 <= to_Z_words (firstn n u_after) < to_Z_words v.
Proof.
  intros u v quot n fuel. revert u v quot n.
  induction fuel as [|fuel' IH];
    intros u v quot n current_i Hlv Hn Hvpos Hlen Hqlen Hfuel Hmsw Hqz;
    [lia|].
  assert (Hci: fuel' = current_i) by lia. subst fuel'.
  simpl knuth_div_loop.
  pose proof (knuth_div_step_correct u v current_i n
    Hlv Hn Hlen Hvpos Hmsw) as Hstep.
  destruct (knuth_div_step u v current_i n) as [u' q_i].
  destruct Hstep as [Heuclid [Hrem [Hlen' [Hout Hmsw_zero]]]].
  change (MakeProofs.set_word) with set_word.
  destruct current_i as [|ci'].
  - (* current_i = 0: last iteration, recursive call has fuel = 0 *)
    simpl knuth_div_loop.
    replace (get_segment u 0 (n + 1)) with (firstn (n + 1) u) in *
      by (unfold get_segment; rewrite skipn_O; reflexivity).
    replace (get_segment u' 0 (n + 1)) with (firstn (n + 1) u') in *
      by (unfold get_segment; rewrite skipn_O; reflexivity).
    rewrite firstn_firstn in Heuclid, Hrem.
    replace (Nat.min n (n + 1)) with n in * by lia.
    replace (0 + n + 1)%nat with (n + 1)%nat by lia.
    split; [|exact Hrem].
    pose proof (Hqz 0%nat ltac:(lia)) as Hq0.
    rewrite (to_Z_words_set_word quot 0%nat q_i ltac:(lia)).
    simpl Z.of_nat. rewrite Z.pow_0_r, Hq0. lia.
  - (* current_i = S ci': recursive call *)
    simpl Nat.pred.
    (* Apply IH *)
    assert (HIH_len: (ci' + n < length u')%nat) by lia.
    assert (HIH_qlen: (ci' < length (set_word quot (S ci') q_i))%nat)
      by (rewrite set_word_length; lia).
    assert (HIH_fuel: S ci' = S ci') by lia.
    (* MSW bound for IH: get_word u' (ci' + n) <= get_word v (n-1) *)
    assert (HIH_msw: to_Z (get_word u' (ci' + n)) <= to_Z (get_word v (n - 1))).
    { set (r := firstn n (get_segment u' (S ci') (n + 1))).
      assert (Hrlen: length r = n)
        by (unfold r; rewrite firstn_length_le
              by (try rewrite Hseg_len; try (rewrite get_segment_length by lia); lia); reflexivity).
      pose proof (remainder_msw_le r v ltac:(lia) ltac:(lia) Hrem) as Hmsw_r.
      rewrite Hrlen, Hlv in Hmsw_r.
      assert (Hgw_r: get_word r (n - 1) = get_word u' (ci' + n)).
      { unfold r, get_word. rewrite nth_firstn.
        replace ((n - 1 <? n)%nat) with true
          by (symmetry; apply Nat.ltb_lt; lia).
        unfold get_segment. rewrite nth_firstn.
        replace ((n - 1 <? n + 1)%nat) with true
          by (symmetry; apply Nat.ltb_lt; lia).
        rewrite nth_skipn. f_equal. lia. }
      rewrite Hgw_r in Hmsw_r. exact Hmsw_r. }
    (* Quotient zeros for IH: positions <= ci' in set_word quot (S ci') q_i *)
    assert (HIH_qz: forall j, (j <= ci')%nat ->
      to_Z (get_word (set_word quot (S ci') q_i) j) = 0).
    { intros j Hj. rewrite get_set_word_other by lia. apply Hqz. lia. }
    pose proof (IH u' v (set_word quot (S ci') q_i) n ci'
      Hlv Hn Hvpos HIH_len HIH_qlen HIH_fuel HIH_msw HIH_qz) as Hloop.
    destruct (knuth_div_loop u' v (set_word quot (S ci') q_i)
      n (S ci') ci') as [u_after quot_final].
    destruct Hloop as [Hinv_rec Hrem_rec].
    split; [|exact Hrem_rec].
    (* Value conservation: combine step equation with IH *)
    rewrite <- Hinv_rec.
    (* Decompose firstn (S ci' + n + 1) u at position S ci' *)
    replace (S ci' + n + 1)%nat with (S ci' + (n + 1))%nat by lia.
    rewrite (to_Z_words_firstn_segment u (S ci') (n + 1) ltac:(lia)).
    rewrite Heuclid.
    (* Decompose firstn (ci' + n + 1) u' at position S ci' *)
    replace (ci' + n + 1)%nat with (S ci' + n)%nat in * by lia.
    rewrite (to_Z_words_firstn_segment u' (S ci') n ltac:(lia)).
    (* firstn (S ci') u' = firstn (S ci') u *)
    assert (Hlow: firstn (S ci') u' = firstn (S ci') u).
    { apply nth_ext with (d := U64.zero) (d' := U64.zero).
      - rewrite !firstn_length_le by lia. reflexivity.
      - intros j Hj. rewrite firstn_length_le in Hj by lia.
        rewrite !nth_firstn.
        replace ((j <? S ci')%nat) with true
          by (symmetry; apply Nat.ltb_lt; lia).
        apply Hout; lia. }
    rewrite Hlow.
    (* get_segment u' (S ci') n = firstn n (get_segment u' (S ci') (n+1)) *)
    assert (Hseg_eq: get_segment u' (S ci') n =
      firstn n (get_segment u' (S ci') (n + 1))).
    { unfold get_segment. rewrite firstn_firstn.
      replace (Nat.min n (n + 1)) with n by lia. reflexivity. }
    rewrite Hseg_eq.
    (* Expand set_word quot (S ci') q_i using quot[S ci'] = 0 *)
    rewrite (to_Z_words_set_word quot (S ci') q_i ltac:(lia)).
    pose proof (Hqz (S ci') ltac:(lia)) as HqSci. rewrite HqSci.
    unfold modulus_words. nia.
Qed.

(** ** Knuth Division — Main Theorem *)

(** knuth_div: full Algorithm D for normalized inputs.
    Preconditions: [length u = m+1], [length v = n], [m >= n > 1],
    and the divisor is normalized (MSB of [v[n-1]] is set). *)
Theorem knuth_div_correct : forall m n u v,
  length u = (m + 1)%nat -> length v = n ->
  (m >= n)%nat -> (n > 1)%nat ->
  to_Z_words v > 0 ->
  to_Z (get_word u m) <= to_Z (get_word v (n - 1)) ->
  let '(u_after, quot) := knuth_div m n u v in
  to_Z_words u = to_Z_words quot * to_Z_words v
    + to_Z_words (firstn n u_after) /\
  0 <= to_Z_words (firstn n u_after) < to_Z_words v.
Proof.
  intros m n u v Hlu Hlv Hmn Hn Hvpos Hmsw.
  unfold knuth_div. change (MakeProofs.extend_words) with extend_words.
  assert (Hmsw': to_Z (get_word u (m - n + n)) <= to_Z (get_word v (n - 1)))
    by (replace (m - n + n)%nat with m by lia; exact Hmsw).
  assert (Hquot_zero: forall j, (j <= m - n)%nat ->
    to_Z (get_word (extend_words (m - n + 1)) j) = 0)
    by (intros; rewrite get_extend_words_Z by lia; reflexivity).
  pose proof (knuth_div_loop_correct u v (extend_words (m - n + 1)) n
    (m - n + 1) (m - n) Hlv Hn Hvpos ltac:(lia)
    ltac:(rewrite extend_words_length; lia)
    ltac:(lia) Hmsw' Hquot_zero)
    as Hloop.
  destruct (knuth_div_loop u v (extend_words (m - n + 1)) n
    (m - n + 1) (m - n)) as [u_after quot_final].
  destruct Hloop as [Hinv Hrem].
  replace (m - n + n + 1)%nat with (m + 1)%nat in Hinv by lia.
  rewrite firstn_all2 in Hinv by lia.
  rewrite to_Z_extend_words, Z.mul_0_l, Z.add_0_r in Hinv.
  exact (conj Hinv Hrem).
Qed.

(** ** Top-Level Division Correctness *)

(** udivrem: general unsigned division dispatcher.
    Handles all cases: division by zero, dividend < divisor,
    single-word, long division, and Knuth multi-word division. *)
(** Helper: value of single-word quotient/remainder stored via set_word *)
Lemma to_Z_words_set_extend : forall n i v,
  (i < n)%nat ->
  to_Z_words (set_word (extend_words n) i v) = to_Z v * (base width) ^ Z.of_nat i.
Proof.
  intros n i v Hi.
  rewrite to_Z_words_set_word by (rewrite extend_words_length; lia).
  rewrite to_Z_extend_words, get_extend_words_Z by lia. lia.
Qed.

(** Helper: padding with zeros preserves value *)
Lemma to_Z_words_app_repeat_zero : forall ws k,
  to_Z_words (ws ++ repeat U64.zero k) = to_Z_words ws.
Proof.
  intros ws k. rewrite to_Z_words_app, to_Z_words_repeat_zero. lia.
Qed.

(** Helper: value of padded remainder equals value of u *)
Lemma to_Z_words_firstn_pad : forall u N m,
  m = count_significant_words u ->
  (m <= N)%nat ->
  to_Z_words (firstn N (u ++ repeat U64.zero N)) = to_Z_words u.
Proof.
  intros u N m Hm HmN.
  rewrite <- (count_significant_words_preserves_value u). rewrite <- Hm.
  assert (Hfm_eq: firstn m (firstn N (u ++ repeat U64.zero N)) = firstn m u).
  { rewrite firstn_firstn, Nat.min_l by lia.
    rewrite firstn_app.
    pose proof (count_significant_words_bound u). rewrite <- Hm in H.
    replace (m - length u)%nat with 0%nat by lia.
    cbn [firstn]. rewrite app_nil_r. reflexivity. }
  rewrite <- Hfm_eq.
  symmetry. apply to_Z_words_firstn_trailing_zeros.
  - rewrite firstn_length_le; [lia|].
    rewrite length_app, repeat_length. pose proof (count_significant_words_bound u).
    rewrite <- Hm in H. lia.
  - intros i Hi.
    assert (HfnLen: length (firstn N (u ++ repeat U64.zero N)) = N).
    { rewrite firstn_length_le; [lia|].
      rewrite length_app, repeat_length. pose proof (count_significant_words_bound u).
      rewrite <- Hm in H. lia. }
    rewrite HfnLen in Hi.
    unfold get_word. rewrite nth_firstn.
    replace ((i <? N)%nat) with true by (symmetry; apply Nat.ltb_lt; lia).
    destruct (Nat.lt_ge_cases i (length u)).
    + rewrite app_nth1 by lia.
      apply (count_significant_words_trailing_zeros u). rewrite <- Hm. lia.
    + rewrite app_nth2 by lia. rewrite nth_repeat. apply spec_zero.
Qed.

(** Helper: single-word value *)
Lemma csw_one_value : forall ws,
  count_significant_words ws = 1%nat ->
  (1 <= length ws)%nat ->
  to_Z_words ws = to_Z (get_word ws 0).
Proof.
  intros ws Hcsw Hlen.
  rewrite <- (count_significant_words_preserves_value ws). rewrite Hcsw.
  destruct ws as [|w ?]; [simpl in Hlen; lia|].
  simpl firstn. unfold get_word. simpl.
  pose proof (spec_to_Z w). lia.
Qed.

Lemma shifted_words_fit : forall ws len s,
  (s < Pos.to_nat U64.width)%nat ->
  length ws = len ->
  (len > 0)%nat ->
  to_Z (get_word ws (len - 1)) > 0 ->
  (1 + to_Z (get_word ws (len - 1))) * 2 ^ Z.of_nat s <= base width ->
  to_Z_words ws * 2 ^ Z.of_nat s < modulus_words len.
Proof.
  intros ws len s Hs Hlen_eq Hlen Hmsw Hbound. subst len.
  set (k := (length ws - 1)%nat).
  rewrite (to_Z_words_firstn_skipn ws k) by lia.
  pose proof (to_Z_words_bound (firstn k ws)) as Hlow.
  rewrite firstn_length_le in Hlow by lia.
  assert (Hskip_eq: to_Z_words (skipn k ws) = to_Z (get_word ws k)).
  { destruct (skipn k ws) as [|w rest] eqn:Hsk.
    - exfalso. assert (length (skipn k ws) = 0%nat) by (rewrite Hsk; reflexivity).
      rewrite length_skipn in H. lia.
    - assert (Hrest: rest = []).
      { assert (Hrl: length (w :: rest) = 1%nat).
        { rewrite <- Hsk. rewrite length_skipn. unfold k. lia. }
        destruct rest; [reflexivity | simpl in Hrl; lia]. }
      subst rest.
      assert (Hw: w = get_word ws k).
      { unfold get_word. symmetry.
        change w with (nth 0 (w :: []) U64.zero).
        rewrite <- Hsk. rewrite nth_skipn. f_equal. unfold k. lia. }
      rewrite Hw. cbn [to_Z_words]. lia. }
  rewrite Hskip_eq.
  assert (Hmod: modulus_words (length ws) = base width * modulus_words k).
  { replace (length ws) with (S k) by (unfold k; lia).
    apply modulus_words_succ. }
  rewrite Hmod. fold k in Hmsw, Hbound.
  pose proof (modulus_words_pos k).
  pose proof (Z.pow_pos_nonneg 2 (Z.of_nat s) ltac:(lia) ltac:(lia)).
  nia.
Qed.

Theorem udivrem_correct : forall M N u v,
  length u = M -> length v = N ->
  to_Z_words v > 0 ->
  let r := udivrem M N u v in
  to_Z_words u =
    to_Z_words (ud_quot r) * to_Z_words v + to_Z_words (ud_rem r) /\
  0 <= to_Z_words (ud_rem r) < to_Z_words v.
Proof.
  intros M N u v HuLen HvLen Hv. unfold udivrem. cbv zeta.
  set (m := count_significant_words u).
  set (n := count_significant_words v).
  pose proof (count_significant_words_bound u) as Hm_bound. fold m in Hm_bound.
  pose proof (count_significant_words_bound v) as Hn_bound. fold n in Hn_bound.
  (* Branch 1: n = 0 — contradiction *)
  destruct (Nat.eqb n 0) eqn:Hn0.
  { apply Nat.eqb_eq in Hn0. exfalso.
    apply count_significant_words_zero in Hn0. lia. }
  apply Nat.eqb_neq in Hn0. assert (Hn_pos: (n > 0)%nat) by lia.
  (* Branch 2: m < n — dividend < divisor *)
  destruct (Nat.ltb m n) eqn:Hmn_lt.
  { apply Nat.ltb_lt in Hmn_lt. cbn [ud_quot ud_rem].
    rewrite to_Z_extend_words.
    rewrite (to_Z_words_firstn_pad u N m eq_refl) by lia.
    split; [lia|].
    split; [pose proof (to_Z_words_bound u); lia|].
    rewrite <- (count_significant_words_preserves_value u). fold m.
    pose proof (to_Z_words_bound (firstn m u)) as Hu_bound.
    rewrite firstn_length_le in Hu_bound by lia.
    pose proof (count_significant_words_lower_bound v Hn_pos) as Hv_lb. fold n in Hv_lb.
    assert (modulus_words m <= modulus_words (n-1)) by (apply modulus_words_le; lia).
    lia. }
  apply Nat.ltb_ge in Hmn_lt.
  (* Branch 3: m = 1 — single word *)
  destruct (Nat.eqb m 1) eqn:Hm1.
  { apply Nat.eqb_eq in Hm1. assert (Hn1: n = 1%nat) by lia.
    assert (Hu_val: to_Z_words u = to_Z (get_word u 0))
      by (apply csw_one_value; [exact Hm1 | lia]).
    assert (Hv_val: to_Z_words v = to_Z (get_word v 0))
      by (apply csw_one_value; [exact Hn1 | lia]).
    assert (Hv0_pos: to_Z (get_word v 0) > 0) by lia.
    assert (H0_lt: to_Z U64.zero < to_Z (get_word v 0)) by (rewrite spec_zero; lia).
    pose proof (spec_div U64.zero (get_word u 0) (get_word v 0) Hv0_pos H0_lt)
      as [q [r [Hdiv_eq [Hdiv_val Hdiv_lt]]]].
    rewrite spec_zero in Hdiv_val.
    cbv beta iota zeta delta [ud_quot ud_rem] in |- *.
    change (MakeProofs.get_word) with get_word.
    rewrite Hdiv_eq.
    change (MakeProofs.set_word) with set_word.
    change (MakeProofs.extend_words) with extend_words.
    rewrite !to_Z_words_set_extend by lia.
    simpl Z.of_nat. rewrite !Z.pow_0_r.
    rewrite Hu_val, Hv_val. pose proof (spec_to_Z r). lia. }
  apply Nat.eqb_neq in Hm1.
  (* Branch 4: n = 1 — long division *)
  destruct (Nat.eqb n 1) eqn:Hn1.
  { apply Nat.eqb_eq in Hn1.
    change (MakeProofs.get_word) with get_word.
    change (MakeProofs.set_word) with set_word.
    change (MakeProofs.extend_words) with extend_words.
    assert (Hv_val: to_Z_words v = to_Z (get_word v 0))
      by (apply csw_one_value; [exact Hn1 | lia]).
    assert (Hv0_pos: to_Z (get_word v 0) > 0) by lia.
    set (ld := long_div (firstn m u) (get_word v 0)).
    pose proof (long_div_correct (firstn m u) (get_word v 0) Hv0_pos) as Hld.
    fold ld in Hld.
    pose proof (long_div_rem_bound (firstn m u) (get_word v 0) Hv0_pos) as Hrem_lt.
    fold ld in Hrem_lt.
    pose proof (long_div_quot_length (firstn m u) (get_word v 0)) as Hql.
    fold ld in Hql. rewrite firstn_length_le in Hql by lia.
    cbn [ud_quot ud_rem].
    rewrite to_Z_words_app_repeat_zero.
    rewrite to_Z_words_set_extend by lia. simpl Z.of_nat. rewrite Z.pow_0_r.
    cbn [ld_quot ld_rem] in Hld.
    rewrite <- (count_significant_words_preserves_value u). fold m.
    rewrite Hv_val. pose proof (spec_to_Z (ld_rem ld)).
    lia. }
  apply Nat.eqb_neq in Hn1.
  (* Branch 5: Knuth division — uses knuth_div_correct (Admitted) *)
  assert (Hm_ge2: (m >= 2)%nat) by lia.
  assert (Hn_ge2: (n >= 2)%nat) by lia.
  change (MakeProofs.get_word) with get_word.
  set (shift := countl_zero (get_word v (n - 1))).
  set (u_norm := shift_left_words (firstn m u) shift).
  set (v_norm := firstn n (shift_left_words (firstn n v) shift)).
  destruct (knuth_div m n u_norm v_norm) as [u_after quot] eqn:Hkd.
  cbn [ud_quot ud_rem].
  rewrite !to_Z_words_app_repeat_zero.
  (* Shift bound *)
  assert (Hshift_bound: (shift < Pos.to_nat U64.width)%nat).
  { unfold shift. apply countl_zero_bound.
    apply (count_significant_words_msw_nonzero v). fold n. lia. }
  (* Lengths for knuth_div_correct preconditions *)
  assert (Hu_norm_len: length u_norm = (m + 1)%nat).
  { unfold u_norm. rewrite shift_left_words_length, firstn_length_le by lia. lia. }
  assert (Hv_norm_len: length v_norm = n).
  { unfold v_norm. rewrite firstn_length_le; [lia|].
    rewrite shift_left_words_length, firstn_length_le by lia. lia. }
  (* Prove Hv_norm_val first (needed for Hv_norm_pos) *)
  assert (Hu_norm_val: to_Z_words u_norm = to_Z_words (firstn m u) * 2 ^ Z.of_nat shift).
  { unfold u_norm. rewrite shift_left_words_correct by exact Hshift_bound. reflexivity. }
  assert (Hfnv_len: length (firstn n v) = n) by (rewrite firstn_length_le; lia).
  assert (Hmsw_pos: to_Z (get_word v (n - 1)) > 0).
  { apply (count_significant_words_msw_nonzero v). fold n. lia. }
  assert (Hgw_eq: get_word (firstn n v) (n - 1) = get_word v (n - 1)).
  { unfold get_word. rewrite nth_firstn.
    replace ((n - 1 <? n)%nat) with true
      by (symmetry; apply Nat.ltb_lt; lia). reflexivity. }
  assert (Hoverflow: to_Z_words (firstn n v) * 2 ^ Z.of_nat shift < modulus_words n).
  { apply (shifted_words_fit _ n); [exact Hshift_bound | exact Hfnv_len | lia | |].
    - rewrite Hgw_eq. exact Hmsw_pos.
    - rewrite Hgw_eq. unfold shift.
      apply countl_zero_succ_shift_le. exact Hmsw_pos. }
  assert (Hv_norm_val: to_Z_words v_norm = to_Z_words (firstn n v) * 2 ^ Z.of_nat shift).
  { unfold v_norm. rewrite <- Hfnv_len at 1.
    apply to_Z_words_firstn_shift_left; [exact Hshift_bound|].
    rewrite Hfnv_len. exact Hoverflow. }
  assert (Hv_norm_pos: to_Z_words v_norm > 0).
  { rewrite Hv_norm_val.
    pose proof (count_significant_words_preserves_value v) as Hcsv.
    fold n in Hcsv.
    assert (to_Z_words (firstn n v) > 0) by lia.
    assert (2 ^ Z.of_nat shift > 0) by (apply Z.lt_gt, Z.pow_pos_nonneg; lia).
    nia. }
  (* MSW bound: overflow word of u_norm <= MSW of v_norm *)
  assert (Hu_norm_msw: to_Z (get_word u_norm m) <= to_Z (get_word v_norm (n - 1))).
  { (* Overflow word < 2^shift *)
    pose proof (shift_left_words_msw_bound (firstn m u) shift
      Hshift_bound ltac:(rewrite firstn_length_le by lia; lia)) as Hu_msw_lt.
    unfold u_norm in Hu_msw_lt.
    rewrite firstn_length_le in Hu_msw_lt by lia.
    (* v_norm MSW >= 2^shift - 1, via value decomposition *)
    pose proof (count_significant_words_lower_bound v Hn_pos) as Hv_lb.
    fold n in Hv_lb.
    assert (Hvn_val_lb: to_Z_words v_norm >= modulus_words (n - 1) * 2 ^ Z.of_nat shift).
    { rewrite Hv_norm_val.
      pose proof (count_significant_words_preserves_value v) as Hcsv.
      fold n in Hcsv. rewrite <- Hcsv in Hv_lb.
      pose proof (modulus_words_pos (n - 1)).
      assert (2 ^ Z.of_nat shift > 0) by (apply Z.lt_gt, Z.pow_pos_nonneg; lia).
      nia. }
    (* Decompose v_norm at position n-1 *)
    rewrite (to_Z_words_firstn_skipn v_norm (n - 1)) in Hvn_val_lb by lia.
    pose proof (to_Z_words_bound (firstn (n - 1) v_norm)) as Hlow_v.
    rewrite firstn_length_le in Hlow_v by lia.
    pose proof (to_Z_words_bound (skipn (n - 1) v_norm)) as Hskip_v.
    rewrite length_skipn, Hv_norm_len in Hskip_v.
    replace (n - (n - 1))%nat with 1%nat in Hskip_v by lia.
    (* skipn (n-1) v_norm has exactly 1 element = v_norm[n-1] *)
    assert (Hskip_eq: to_Z_words (skipn (n - 1) v_norm) = to_Z (get_word v_norm (n - 1))).
    { destruct (skipn (n - 1) v_norm) as [|w rest] eqn:Hsk.
      - exfalso. assert (length (skipn (n-1) v_norm) = 0%nat) by (rewrite Hsk; reflexivity).
        rewrite length_skipn, Hv_norm_len in *. lia.
      - assert (Hrest: rest = []).
        { assert (length (w :: rest) = 1%nat)
            by (rewrite <- Hsk, length_skipn, Hv_norm_len; lia).
          destruct rest; [reflexivity | simpl in *; lia]. }
        subst rest. cbn [to_Z_words].
        assert (Hw: w = get_word v_norm (n - 1)).
        { unfold get_word. change w with (nth 0 (w :: []) U64.zero).
          rewrite <- Hsk. rewrite nth_skipn. f_equal. lia. }
        rewrite Hw. lia. }
    rewrite Hskip_eq in Hvn_val_lb.
    pose proof (modulus_words_pos (n - 1)) as HM.
    set (MW := modulus_words (n - 1)) in *.
    set (vlow := to_Z_words (firstn (n - 1) v_norm)) in *.
    set (vmsw := to_Z (get_word v_norm (n - 1))) in *.
    set (sh := 2 ^ Z.of_nat shift) in *.
    (* vmsw >= sh *)
    (* Derive vmsw >= sh, then overflow < sh <= vmsw *)
    destruct (Z.le_gt_cases sh vmsw).
    + (* sh <= vmsw: done *) exact (Z.le_trans _ _ _ (Z.lt_le_incl _ _ Hu_msw_lt) H).
    + (* sh > vmsw: contradiction *)
      exfalso.
      assert (H0_MW: 0 <= MW) by (unfold MW; pose proof (modulus_words_pos (n-1)); lia).
      assert (H0_le: vmsw <= sh - 1) by (unfold vmsw, sh in *; lia).
      pose proof (Z.mul_le_mono_nonneg_l vmsw (sh - 1) MW H0_MW H0_le).
      eapply (Z_mul_le_contradiction vlow MW vmsw sh);
        [exact HM | exact Hlow_v | exact Hvn_val_lb | exact H0]. }
  (* Apply knuth_div_correct *)
  pose proof (knuth_div_correct m n u_norm v_norm
    Hu_norm_len Hv_norm_len ltac:(lia) ltac:(lia) Hv_norm_pos Hu_norm_msw) as Hknuth.
  rewrite Hkd in Hknuth. destruct Hknuth as [Hknuth_eq Hknuth_rem].
  rewrite shift_right_words_correct by exact Hshift_bound.
  rewrite <- (count_significant_words_preserves_value u). fold m.
  rewrite <- (count_significant_words_preserves_value v). fold n.
  rewrite Hu_norm_val in Hknuth_eq. rewrite Hv_norm_val in Hknuth_eq, Hknuth_rem.
  set (s := 2 ^ Z.of_nat shift) in *.
  assert (Hs_pos: s > 0) by (unfold s; apply Z.lt_gt, Z.pow_pos_nonneg; lia).
  (* rem_norm is divisible by s (from Euclidean equation) *)
  assert (Hrem_div: to_Z_words (firstn n u_after) mod s = 0).
  { assert (Heq: to_Z_words (firstn n u_after) =
      (to_Z_words (firstn m u) - to_Z_words (firstn n v) * to_Z_words quot) * s) by nia.
    rewrite Heq. apply Z_mod_mult. }
  pose proof (Z_div_mod_eq_full (to_Z_words (firstn n u_after)) s) as Hdm.
  rewrite Hrem_div, Z.add_0_r in Hdm.
  split.
  - nia.
  - split.
    + apply Z.div_pos; lia.
    + apply Z.div_lt_upper_bound; lia.
Qed.

(** Specialization to 256-bit (4-word) operands.
    Follows directly from udivrem_correct once it is fully proved. *)
Theorem udivrem256_correct : forall u v,
  length u = 4%nat -> length v = 4%nat ->
  to_Z_words v > 0 ->
  let r := udivrem 4 4 u v in
  to_Z_words u =
    to_Z_words (ud_quot r) * to_Z_words v + to_Z_words (ud_rem r) /\
  0 <= to_Z_words (ud_rem r) < to_Z_words v.
Proof.
  intros. apply udivrem_correct; assumption.
Qed.

End MakeProofs.
