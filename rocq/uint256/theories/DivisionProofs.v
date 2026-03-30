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
  assert (Hw_eq: 2^w = 2^s * 2^(w-s))
    by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
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
  assert (Hpow_eq: 2^w = 2^s * 2^(w - s)).
  { rewrite <- Z.pow_add_r by lia. f_equal. lia. }
  rewrite Hpow_eq.
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
  assert (Hpow: base width = 2 ^ s * 2 ^ (Z.pos width - s)).
  { unfold base. rewrite <- Z.pow_add_r by lia. f_equal. lia. }
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
    cbn [ld_quot length]. rewrite IH. reflexivity.
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
  - unfold long_div_fold; fold long_div_fold. cbn [ld_quot ld_rem].
    pose proof (spec_div _ u _ Hv Hrem) as Hdiv.
    destruct (div rem u v) as [q rm].
    destruct Hdiv as [Hdiv_eq Hdiv_lt].
    cbn [fst snd].
    set (rec := long_div_fold rest v rm).
    pose proof (IH v rm Hv Hdiv_lt) as HIH.
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
        assert (2 ^ (64 - Z.of_nat s) * 2 ^ Z.of_nat s = 2 ^ 64)
          by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
        nia.
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
      assert (Hpow: 2 ^ (64 - Z.of_nat s) * 2 ^ Z.of_nat s = 2 ^ 64).
      { rewrite <- Z.pow_add_r by lia. f_equal. lia. }
      nia.
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
        assert (2 ^ Z.of_nat s * 2 ^ (64 - Z.of_nat s) = 2 ^ 64)
          by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
        nia.
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
      assert (Hpow: 2 ^ Z.of_nat s * 2 ^ (64 - Z.of_nat s) = 2 ^ 64).
      { rewrite <- Z.pow_add_r by lia. f_equal. lia. }
      nia. }
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

(** Shift-left then shift-right is division (round-trip for aligned values). *)
Lemma shift_right_left_cancel : forall ws shift,
  (shift < Pos.to_nat U64.width)%nat ->
  to_Z_words ws mod 2 ^ (Z.of_nat shift) = 0 ->
  to_Z_words (shift_right_words (firstn (length ws) (shift_left_words ws shift)) shift) =
    to_Z_words ws.
Proof. Admitted.

(** ** Knuth Subtract-and-Correct *)

(** knuth_sub_loop computes [u_seg - q_hat * v] with borrow propagation.
    The mathematical value of the segment decreases by [q_hat * v_val],
    modulo the segment width, with the borrow [k] tracking the overflow. *)
Lemma knuth_sub_loop_correct : forall u_seg q_hat vs j k,
  length u_seg = (j + length vs)%nat ->
  let '(u', k') := knuth_sub_loop u_seg q_hat vs j k in
  to_Z_words u' + U128.to_Z k' * modulus_words (j + length vs) =
    to_Z_words u_seg - (U128.to_Z q_hat * to_Z_words vs - U128.to_Z k)
      * base width ^ (Z.of_nat j).
Proof. Admitted.

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
    to_Z q_final * to_Z_words v + to_Z_words (firstn n u_after) /\
  0 <= to_Z_words (firstn n u_after) < to_Z_words v.
Proof. Admitted.

(** ** Knuth Division — Single Step and Loop *)

(** knuth_div_step: one iteration combining estimate + subtract + correct. *)
Lemma knuth_div_step_correct : forall u v i n,
  length v = n -> (n > 1)%nat ->
  (i + n < length u)%nat ->
  to_Z_words v > 0 ->
  let '(u', q_i) := knuth_div_step u v i n in
  to_Z_words (get_segment u i (n + 1)) =
    to_Z q_i * to_Z_words v + to_Z_words (firstn n (get_segment u' i (n + 1))) /\
  0 <= to_Z_words (firstn n (get_segment u' i (n + 1))) < to_Z_words v.
Proof. Admitted.

(** knuth_div_loop: the outer loop iterating from [m-n] down to [0].
    Invariant: the mathematical quotient is accumulated in [quot],
    and [u] is progressively reduced. *)
Lemma knuth_div_loop_correct : forall u v quot n fuel current_i,
  length v = n -> (n > 1)%nat ->
  to_Z_words v > 0 ->
  let '(u_after, quot_final) := knuth_div_loop u v quot n fuel current_i in
  to_Z_words u =
    to_Z_words quot_final * to_Z_words v + to_Z_words (firstn n u_after) /\
  0 <= to_Z_words (firstn n u_after) < to_Z_words v.
Proof. Admitted.

(** ** Knuth Division — Main Theorem *)

(** knuth_div: full Algorithm D for normalized inputs.
    Preconditions: [length u = m+1], [length v = n], [m >= n > 1],
    and the divisor is normalized (MSB of [v[n-1]] is set). *)
Theorem knuth_div_correct : forall m n u v,
  length u = (m + 1)%nat -> length v = n ->
  (m >= n)%nat -> (n > 1)%nat ->
  to_Z_words v > 0 ->
  let '(u_after, quot) := knuth_div m n u v in
  to_Z_words u = to_Z_words quot * to_Z_words v
    + to_Z_words (firstn n u_after) /\
  0 <= to_Z_words (firstn n u_after) < to_Z_words v.
Proof. Admitted.

(** ** Top-Level Division Correctness *)

(** udivrem: general unsigned division dispatcher.
    Handles all cases: division by zero, dividend < divisor,
    single-word, long division, and Knuth multi-word division. *)
Theorem udivrem_correct : forall M N u v,
  length u = M -> length v = N ->
  to_Z_words v > 0 ->
  let r := udivrem M N u v in
  to_Z_words u =
    to_Z_words (ud_quot r) * to_Z_words v + to_Z_words (ud_rem r) /\
  0 <= to_Z_words (ud_rem r) < to_Z_words v.
Proof. Admitted.

(** Specialization to 256-bit (4-word) operands. *)
Theorem udivrem256_correct : forall u v,
  length u = 4%nat -> length v = 4%nat ->
  to_Z_words v > 0 ->
  let r := udivrem 4 4 u v in
  to_Z_words u =
    to_Z_words (ud_quot r) * to_Z_words v + to_Z_words (ud_rem r) /\
  0 <= to_Z_words (ud_rem r) < to_Z_words v.
Proof. Admitted.

End MakeProofs.
