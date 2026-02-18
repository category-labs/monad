(** * Runtime Multiplication Proofs

    Correctness proofs for the runtime multiplication model
    defined in RuntimeMul.v.

    Structure (bottom-up):
    5. adc_2_short_correct, adc_2_full_correct, adc_3_correct — primitive lemmas
    4. mul_line_recur / mul_add_line_recur correctness
    3. mul_line_correct / mul_add_line_correct — row correctness
    2. truncating_mul_runtime_correct — general word-list version
    1. truncating_mul256_runtime_correct — main 256-bit theorem
*)

From Stdlib Require Import ZArith Lia List.
From Uint256 Require Import Primitives Words WordsLemmas RuntimeMul.
Import ListNotations.
Open Scope Z_scope.

(** * General Modular Arithmetic Helper *)

Lemma Z_mod_divide_diff : forall a b n,
  n <> 0 ->
  (exists k, a - b = k * n) ->
  a mod n = b mod n.
Proof.
  intros a b n Hn [k Hk].
  replace a with (b + k * n) by lia.
  apply Z_mod_plus_full.
Qed.

(** * Level 5: Primitive Correctness *)

(** adc_2_short computes exact 128-bit sum.
    Requires x_1 <= modulus64 - 2 (e.g., x_1 = hi(mulx64 a b))
    to ensure the sum fits in 128 bits. *)
Lemma adc_2_short_correct : forall x_1 x_0 y_0,
  0 <= x_1 <= modulus64 - 2 ->
  0 <= x_0 < modulus64 ->
  0 <= y_0 < modulus64 ->
  let '(r_1, r_0) := adc_2_short x_1 x_0 y_0 in
  r_1 * modulus64 + r_0 = x_1 * modulus64 + x_0 + y_0 /\
  0 <= r_0 < modulus64 /\
  0 <= r_1 < modulus64.
Proof.
  intros x_1 x_0 y_0 Hx1 Hx0 Hy0.
  unfold adc_2_short. cbn [fst snd].
  set (sum := x_1 * modulus64 + x_0 + y_0).
  assert (Hsum_nn: 0 <= sum) by (unfold sum, modulus64; lia).
  assert (Hmod: 0 < modulus64) by (unfold modulus64; lia).
  pose proof (Z_div_mod_eq_full sum modulus64) as Hdm.
  pose proof (Z.mod_pos_bound sum modulus64 Hmod) as Hmod_bound.
  split.
  - lia.
  - split; [lia|].
    split.
    + apply Z.div_pos; lia.
    + apply Z.div_lt_upper_bound; [lia|].
      unfold sum. unfold modulus64 in *. nia.
Qed.

(** adc_2_full computes 128-bit sum modulo 2^128 *)
Lemma adc_2_full_correct : forall x_1 x_0 y_1 y_0,
  0 <= x_1 < modulus64 ->
  0 <= x_0 < modulus64 ->
  0 <= y_1 < modulus64 ->
  0 <= y_0 < modulus64 ->
  let '(r_1, r_0) := adc_2_full x_1 x_0 y_1 y_0 in
  r_1 * modulus64 + r_0
  = (x_1 * modulus64 + x_0 + y_1 * modulus64 + y_0) mod (modulus64 * modulus64) /\
  0 <= r_0 < modulus64 /\
  0 <= r_1 < modulus64.
Proof.
  intros x_1 x_0 y_1 y_0 Hx1 Hx0 Hy1 Hy0.
  unfold adc_2_full. cbn [fst snd].
  set (sum := x_1 * modulus64 + x_0 + y_1 * modulus64 + y_0).
  set (M := modulus64).
  set (sum_mod := sum mod (M * M)).
  assert (HM: 0 < M) by (unfold M, modulus64; lia).
  assert (HMM: 0 < M * M) by lia.
  pose proof (Z.mod_pos_bound sum (M * M) HMM) as Hmod_bound.
  pose proof (Z_div_mod_eq_full sum_mod M) as Hdm.
  pose proof (Z.mod_pos_bound sum_mod M HM) as Hmod_bound2.
  split.
  - lia.
  - split; [lia|].
    split.
    + apply Z.div_pos; lia.
    + apply Z.div_lt_upper_bound; [lia|].
      unfold sum_mod. lia.
Qed.

(** adc_3 computes exact 192-bit sum (when x_2 is small enough) *)
Lemma adc_3_correct : forall x_2 x_1 x_0 y_1 y_0,
  0 <= x_2 ->
  0 <= x_1 < modulus64 ->
  0 <= x_0 < modulus64 ->
  0 <= y_1 < modulus64 ->
  0 <= y_0 < modulus64 ->
  let '(r_2, r_1, r_0) := adc_3 x_2 x_1 x_0 y_1 y_0 in
  r_2 * modulus64 * modulus64 + r_1 * modulus64 + r_0
  = x_2 * modulus64 * modulus64 + x_1 * modulus64 + x_0 + y_1 * modulus64 + y_0 /\
  0 <= r_0 < modulus64 /\
  0 <= r_1 < modulus64.
Proof.
  intros x_2 x_1 x_0 y_1 y_0 Hx2 Hx1 Hx0 Hy1 Hy0.
  unfold adc_3. cbn [fst snd].
  set (sum := x_2 * modulus64 * modulus64
            + x_1 * modulus64 + x_0
            + y_1 * modulus64 + y_0).
  set (M := modulus64).
  assert (HM: 0 < M) by (unfold M, modulus64; lia).
  assert (HMM: 0 < M * M) by lia.
  assert (Hsum_nn: 0 <= sum) by (unfold sum; nia).
  pose proof (Z_div_mod_eq_full sum (M * M)) as Hdm1.
  pose proof (Z.mod_pos_bound sum (M * M) HMM) as Hmod1.
  pose proof (Z_div_mod_eq_full (sum mod (M * M)) M) as Hdm2.
  pose proof (Z.mod_pos_bound (sum mod (M * M)) M HM) as Hmod2.
  pose proof (Z.mod_pos_bound sum M HM) as Hmod3.
  split.
  - rewrite (Znumtheory.Zmod_div_mod M (M * M) sum HM HMM ltac:(exists M; ring)).
    nia.
  - split; [lia|].
    split.
    + apply Z.div_pos; lia.
    + apply Z.div_lt_upper_bound; lia.
Qed.

(** ** Additional Helpers *)

(** Tight bound on mulx64 high word: at most modulus64 - 2.
    This is because x*y <= (M-1)^2 = M^2-2M+1 < (M-1)*M. *)
Lemma mulx64_hi_le : forall x y,
  0 <= x < modulus64 ->
  0 <= y < modulus64 ->
  to_Z64 (hi (mulx64 x y)) <= modulus64 - 2.
Proof.
  intros x y Hx Hy.
  unfold mulx64, hi, from_Z64, to_Z64.
  rewrite Z.shiftr_div_pow2 by lia.
  assert (Hprod: x * y < (modulus64 - 1) * modulus64)
    by (unfold modulus64 in *; nia).
  pose proof (Z.div_lt_upper_bound (x * y) modulus64 (modulus64 - 1)
    ltac:(unfold modulus64; lia) Hprod).
  unfold modulus64 in *. lia.
Qed.

(** adc_3 high output is bounded when x_2 <= modulus64 - 2
    (which is always the case when x_2 = hi(mulx64 a b)). *)
Lemma adc_3_r2_bounded : forall x_2 x_1 x_0 y_1 y_0,
  0 <= x_2 <= modulus64 - 2 ->
  0 <= x_1 < modulus64 ->
  0 <= x_0 < modulus64 ->
  0 <= y_1 < modulus64 ->
  0 <= y_0 < modulus64 ->
  let '(r_2, _, _) := adc_3 x_2 x_1 x_0 y_1 y_0 in
  0 <= r_2 < modulus64.
Proof.
  intros x_2 x_1 x_0 y_1 y_0 Hx2 Hx1 Hx0 Hy1 Hy0.
  unfold adc_3. cbn [fst snd].
  set (sum := x_2 * modulus64 * modulus64
            + x_1 * modulus64 + x_0 + y_1 * modulus64 + y_0).
  set (M := modulus64).
  assert (HMM: 0 < M * M) by (unfold M, modulus64; lia).
  split.
  - apply Z.div_pos; [unfold sum, M, modulus64 in *; nia | lia].
  - apply Z.div_lt_upper_bound; [lia|].
    unfold sum, M, modulus64 in *. nia.
Qed.

(** get_word from a valid word list is bounded *)
Lemma get_word_bounded : forall ws i,
  words_valid ws ->
  (i < length ws)%nat ->
  0 <= get_word ws i < modulus64.
Proof.
  intros ws i Hvalid Hi.
  unfold get_word, words_valid in *.
  apply Forall_nth; [exact Hvalid | exact Hi].
Qed.

(** * Level 4: Recursive Helper Correctness *)

(** ** mul_line_recur *)

Lemma mul_line_recur_length : forall xs y result I R carry,
  length result = R ->
  length (mul_line_recur xs y result I R carry) = R.
Proof.
  induction xs as [|x rest IH]; intros y result I R carry Hlen.
  - cbn [mul_line_recur].
    destruct (I <? R)%nat.
    + rewrite set_word_length. exact Hlen.
    + exact Hlen.
  - cbn [mul_line_recur].
    destruct (I <? R)%nat.
    + destruct (I + 1 <? R)%nat.
      * destruct (adc_2_short _ _ _) as [nc ri] eqn:Hadc.
        apply IH. rewrite set_word_length. exact Hlen.
      * rewrite set_word_length. exact Hlen.
    + exact Hlen.
Qed.

Lemma mul_line_recur_valid : forall xs y result I R carry,
  words_valid xs ->
  0 <= y < modulus64 ->
  0 <= carry < modulus64 ->
  words_valid result ->
  length result = R ->
  words_valid (mul_line_recur xs y result I R carry).
Proof.
  induction xs as [|x rest IH]; intros y result I R carry
    Hxs Hy Hcarry Hresult Hlen.
  - cbn [mul_line_recur].
    destruct (I <? R)%nat.
    + apply set_word_valid; assumption.
    + assumption.
  - cbn [mul_line_recur].
    inversion Hxs as [|x' rest' Hx Hrest]; subst x' rest'.
    destruct (I <? R)%nat eqn:HIR.
    + destruct (I + 1 <? R)%nat eqn:HIR1.
      * pose proof (mulx64_hi_bounded x y Hx Hy) as Hhi.
        pose proof (mulx64_lo_bounded x y Hx Hy) as Hlo.
        pose proof (mulx64_hi_le x y Hx Hy) as Hhile.
        pose proof (adc_2_short_correct (hi (mulx64 x y)) (lo (mulx64 x y))
                      carry (conj (proj1 Hhi) Hhile) Hlo Hcarry) as Hadc.
        destruct (adc_2_short (hi (mulx64 x y)) (lo (mulx64 x y)) carry)
          as [nc ri] eqn:Hadc_eq.
        destruct Hadc as [_ [Hri Hnc]].
        apply IH.
        -- exact Hrest.
        -- exact Hy.
        -- exact Hnc.
        -- apply set_word_valid; [exact Hresult | exact Hri].
        -- rewrite set_word_length. exact Hlen.
      * apply set_word_valid; [exact Hresult|].
        unfold normalize64. apply Z.mod_pos_bound. unfold modulus64. lia.
    + exact Hresult.
Qed.

(** mul_line_recur accumulates x[I..M-1] * y into result[I..] with carry.
    Precondition: result positions I..R-1 must be zero (mul_line initializes to zeros).
**)
Lemma mul_line_recur_correct : forall xs y result I R carry,
  words_valid xs ->
  0 <= y < modulus64 ->
  0 <= carry < modulus64 ->
  words_valid result ->
  length result = R ->
  (I <= R)%nat ->
  (forall j, (I <= j)%nat -> (j < R)%nat -> get_word result j = 0) ->
  to_Z_words (mul_line_recur xs y result I R carry) mod modulus_words R
  = (to_Z_words result +
       (to_Z_words xs * to_Z64 y + to_Z64 carry) * 2^(64 * Z.of_nat I))
    mod modulus_words R.
Proof.
  induction xs as [|x rest IH]; intros y result I R carry
    Hxs Hy Hcarry Hresult Hlen HIR Hzeros.
  - cbn [mul_line_recur to_Z_words].
    rewrite Z.mul_0_l, Z.add_0_l. unfold to_Z64 at 1.
    destruct (I <? R)%nat eqn:HIR'.
    + (* I < R: set_word result I carry *)
      apply Nat.ltb_lt in HIR'.
      rewrite to_Z_words_set_word by (try lia; assumption).
      rewrite Hzeros by lia. unfold to_Z64 at 1.
      rewrite Z.mul_0_l, Z.sub_0_r. reflexivity.
    + (* I = R: carry falls off the end *)
      apply Nat.ltb_ge in HIR'.
      assert (I = R) by lia. subst I.
      unfold modulus_words, words_bits.
      rewrite Z.mul_comm. rewrite Z_mod_plus_full. reflexivity.
  - (* xs = x :: rest *)
    cbn [mul_line_recur].
    inversion Hxs as [|x' rest' Hx Hrest]; subst x' rest'.
    destruct (I <? R)%nat eqn:HIR'.
    + apply Nat.ltb_lt in HIR'.
      destruct (I + 1 <? R)%nat eqn:HIR1.
      * (* Normal case: mulx + adc_2_short, then recurse *)
        apply Nat.ltb_lt in HIR1.
        pose proof (mulx64_hi_bounded x y Hx Hy) as Hhi.
        pose proof (mulx64_lo_bounded x y Hx Hy) as Hlo.
        pose proof (mulx64_hi_le x y Hx Hy) as Hhile.
        pose proof (mulx64_correct x y ltac:(lia) ltac:(lia)) as Hmulx.
        pose proof (adc_2_short_correct (hi (mulx64 x y)) (lo (mulx64 x y))
                      carry (conj (proj1 Hhi) Hhile) Hlo Hcarry) as Hadc.
        destruct (adc_2_short (hi (mulx64 x y)) (lo (mulx64 x y)) carry)
          as [nc ri] eqn:Hadc_eq.
        destruct Hadc as [Hadc_main [Hri Hnc]].
        (* Apply IH *)
        rewrite IH; try assumption.
        -- (* Arithmetic: show the mod expressions are equal *)
           rewrite to_Z_words_set_word
             by (try rewrite set_word_length; try lia; assumption).
           rewrite Hzeros by lia. unfold to_Z64 at 2.
           rewrite Z.mul_0_l, Z.sub_0_r.
           f_equal.
           (* Key: ri + nc * 2^64 = x * y + carry (from mulx + adc) *)
           cbn [to_Z_words]. unfold to_Z64 in *.
           rewrite Z.shiftl_mul_pow2 in Hmulx by lia.
           rewrite Nat2Z.inj_succ.
           replace (64 * Z.succ (Z.of_nat I))
             with (64 + 64 * Z.of_nat I) by lia.
           rewrite Z.pow_add_r by lia.
           repeat rewrite Z.mul_add_distr_r.
           rewrite Hmulx.
           replace (to_Z_words result +
                      ri * 2 ^ (64 * Z.of_nat I) +
                     (to_Z_words rest * y * (2 ^ 64 * 2 ^ (64 * Z.of_nat I)) +
                        nc * (2 ^ 64 * 2 ^ (64 * Z.of_nat I)))) with
             (to_Z_words result + (nc * 2 ^ 64 + ri) * 2 ^ (64 * Z.of_nat I) +
                     (to_Z_words rest * y * (2 ^ 64 * 2 ^ (64 * Z.of_nat I)))) by lia.
           unfold modulus64 in Hadc_main. rewrite Hadc_main.
           lia.
        -- apply set_word_valid; [exact Hresult | exact Hri].
        -- rewrite set_word_length. exact Hlen.
        -- intros j Hj1 Hj2.
           rewrite get_set_word_other by lia.
           apply Hzeros; lia.
      * (* Last word: I+1 >= R, so I = R-1. Truncate to 64 bits. *)
        apply Nat.ltb_ge in HIR1.
        assert (HI_eq: I = (R - 1)%nat) by lia.
        rewrite to_Z_words_set_word; [| lia | assumption|].
        2: unfold normalize64, modulus64; apply Z.mod_pos_bound; lia.
        rewrite Hzeros by lia. unfold to_Z64 at 1.
        rewrite Z.mul_0_l, Z.sub_0_r.
        cbn [to_Z_words]. unfold to_Z64, normalize64.
        (* Let M denote modulus_words R.
         * Then M = modulus64 * 2^(64*I) since I+1 = R *)
        assert (HM: modulus_words R = modulus64 * 2^(64 * Z.of_nat I)).
        { unfold modulus_words, words_bits, modulus64.
          rewrite <- Z.pow_add_r by lia. f_equal. lia. }
        set (P := 2^(64 * Z.of_nat I)) in HM |-*.
        set (v := y * x + carry).
        (* RHS has (x + 2^64 * to_Z_words rest) * y + carry = v + 2^64 * to_Z_words rest * y *)
        (* Difference from LHS is a multiple of M = 2^64 * P *)
        pose proof (Z_div_mod_eq_full v modulus64) as Hdm.
        replace (((x + 2^64 * to_Z_words rest) * y + carry) * P)
          with ((v mod 2^64) * P +
                  (v / 2^64 + to_Z_words rest * y) * (2^64 * P))
          by (unfold modulus64 in *; nia).
        rewrite HM, Z.add_assoc, Z_mod_plus_full. reflexivity.
    + (* I >= R: result unchanged, product term vanishes mod M *)
      apply Nat.ltb_ge in HIR'.
      assert (I = R) by lia. subst I.
      cbn [to_Z_words]. unfold to_Z64.
      unfold modulus_words, words_bits.
      rewrite (Z.mul_comm 64 (Z.of_nat R)).
      rewrite Z_mod_plus_full. reflexivity.
Qed.

(** ** mul_add_line_recur *)

Lemma mul_add_line_recur_length : forall xs_tail y_i result J I R c_hi c_lo,
  length result = R ->
  length (mul_add_line_recur xs_tail y_i result J I R c_hi c_lo) = R.
Proof.
  induction xs_tail as [|x rest IH]; intros y_i result J I R c_hi c_lo Hlen.
  - cbn [mul_add_line_recur].
    destruct (I + J + 1 <? R)%nat eqn:H1.
    + destruct (adc_2_short c_hi c_lo (get_word result (I + J))) as [r1 r0].
      rewrite set_word_length, set_word_length. exact Hlen.
    + destruct (I + J <? R)%nat.
      * rewrite set_word_length. exact Hlen.
      * exact Hlen.
  - cbn [mul_add_line_recur].
    destruct (I + J <? R)%nat eqn:H1.
    + destruct (I + J + 2 <? R)%nat eqn:H2.
      * destruct (adc_3 _ _ _ _ _) as [[c_hi' c_lo'] res_IJ].
        apply IH. rewrite set_word_length. exact Hlen.
      * destruct (I + J + 1 <? R)%nat eqn:H3.
        -- destruct (adc_2_full _ _ _ _) as [c_lo' res_IJ].
           apply IH. rewrite set_word_length. exact Hlen.
        -- apply IH. rewrite set_word_length. exact Hlen.
    + exact Hlen.
Qed.

Lemma mul_add_line_recur_valid : forall xs_tail y_i result J I R c_hi c_lo,
  words_valid xs_tail ->
  0 <= y_i < modulus64 ->
  0 <= c_hi < modulus64 ->
  0 <= c_lo < modulus64 ->
  words_valid result ->
  length result = R ->
  (R <= I + J + length xs_tail + 1)%nat ->
  words_valid (mul_add_line_recur xs_tail y_i result J I R c_hi c_lo).
Proof.
  induction xs_tail as [|x rest IH]; intros y_i result J I R c_hi c_lo
    Hxs Hyi Hchi Hclo Hresult Hlen HRI.
  - (* Base: flush carry — adc_2_short path is unreachable *)
    cbn [mul_add_line_recur length] in *.
    destruct (I + J + 1 <? R)%nat eqn:H1.
    + apply Nat.ltb_lt in H1. lia.
    + destruct (I + J <? R)%nat.
      * apply set_word_valid; [assumption|].
        unfold normalize64. apply Z.mod_pos_bound. unfold modulus64. lia.
      * exact Hresult.
  - (* Inductive: process next word *)
    cbn [mul_add_line_recur].
    inversion Hxs as [|x' rest' Hx Hrest]; subst.
    cbn [length] in HRI.
    destruct (I + J <? length result)%nat eqn:H1.
    + apply Nat.ltb_lt in H1.
      destruct (I + J + 2 <? length result)%nat eqn:H2.
      * (* Full case: mulx + adc_3 *)
        pose proof (mulx64_hi_bounded x y_i Hx Hyi) as Hhi.
        pose proof (mulx64_lo_bounded x y_i Hx Hyi) as Hlo.
        pose proof (mulx64_hi_le x y_i Hx Hyi) as Hhile.
        unfold to_Z64 in Hhi, Hlo, Hhile.
        pose proof (get_word_bounded result (I + J) Hresult ltac:(lia)) as Hgw.
        pose proof (adc_3_correct (hi (mulx64 x y_i)) (lo (mulx64 x y_i))
          (get_word result (I + J)) c_hi c_lo
          ltac:(lia) Hlo Hgw Hchi Hclo) as Hadc3.
        pose proof (adc_3_r2_bounded (hi (mulx64 x y_i)) (lo (mulx64 x y_i))
          (get_word result (I + J)) c_hi c_lo
          ltac:(lia) Hlo Hgw Hchi Hclo) as Hr2.
        destruct (adc_3 (hi (mulx64 x y_i)) (lo (mulx64 x y_i))
          (get_word result (I + J)) c_hi c_lo) as [[c_hi' c_lo'] res_IJ].
        destruct Hadc3 as [_ [Hres_IJ Hclo']].
        apply IH.
        -- exact Hrest.
        -- exact Hyi.
        -- exact Hr2.
        -- exact Hclo'.
        -- apply set_word_valid; [exact Hresult | exact Hres_IJ].
        -- rewrite set_word_length. reflexivity.
        -- lia.
      * destruct (I + J + 1 <? length result)%nat eqn:H3.
        -- (* Second-to-last: mulx low + adc_2_full *)
           pose proof (adc_2_full_correct (normalize64 (x * y_i))
             (get_word result (I + J)) c_hi c_lo
             ltac:(unfold normalize64; split;
               [apply Z.mod_pos_bound; unfold modulus64; lia |
                apply Z.mod_pos_bound; unfold modulus64; lia])
             ltac:(apply get_word_bounded; [assumption | lia]) Hchi Hclo) as Hadc2.
           destruct (adc_2_full (normalize64 (x * y_i))
             (get_word result (I + J)) c_hi c_lo) as [c_lo' res_IJ].
           destruct Hadc2 as [_ [Hres_IJ Hclo']].
           apply IH.
           ++ exact Hrest.
           ++ exact Hyi.
           ++ unfold modulus64; lia.
           ++ exact Hclo'.
           ++ apply set_word_valid; [exact Hresult | exact Hres_IJ].
           ++ rewrite set_word_length. reflexivity.
           ++ lia.
        -- (* Last position: result[I+J] += c_lo *)
           apply IH.
           ++ exact Hrest.
           ++ exact Hyi.
           ++ exact Hchi.
           ++ exact Hclo.
           ++ apply set_word_valid; [exact Hresult|].
              unfold normalize64. apply Z.mod_pos_bound. unfold modulus64. lia.
           ++ rewrite set_word_length. reflexivity.
           ++ lia.
    + exact Hresult.
Qed.

(** mul_add_line_recur accumulates partial products with 2-word carry.
    Precondition: I + J + length xs_tail + 1 >= R ensures the carry flush
    (adc_2_short overwrite) never executes, so carry is always dropped. *)
Lemma mul_add_line_recur_correct : forall xs_tail y_i result J I R c_hi c_lo,
  words_valid xs_tail ->
  0 <= y_i < modulus64 ->
  0 <= c_hi < modulus64 ->
  0 <= c_lo < modulus64 ->
  words_valid result ->
  length result = R ->
  (R <= I + J + length xs_tail + 1)%nat ->
  to_Z_words (mul_add_line_recur xs_tail y_i result J I R c_hi c_lo)
    mod modulus_words R
  = (to_Z_words result
     + (to_Z_words xs_tail * to_Z64 y_i * modulus64
        + to_Z64 c_hi * modulus64 + to_Z64 c_lo)
       * 2^(64 * Z.of_nat (I + J)))
    mod modulus_words R.
Proof.
  induction xs_tail as [|x rest IH]; intros y_i result J I R c_hi c_lo
    Hxs Hyi Hchi Hclo Hresult Hlen HRI.
  - (* Base case: xs_tail = [] — flush carry *)
    cbn [mul_add_line_recur length] in *.
    cbn [to_Z_words]. rewrite Z.mul_0_l, Z.add_0_l.
    set (pos := (I + J)%nat).
    destruct (pos + 1 <? R)%nat eqn:H1.
    + (* pos + 1 < R: impossible — R <= pos + 1 from HRI *)
      apply Nat.ltb_lt in H1. lia.
    + destruct (pos <? R)%nat eqn:H2.
      * (* pos < R, pos + 1 >= R: pos = R - 1. Add c_lo, drop c_hi *)
        apply Nat.ltb_ge in H1. apply Nat.ltb_lt in H2.
        assert (Hpos: pos = (R - 1)%nat) by lia.
        rewrite to_Z_words_set_word.
        2: subst pos; lia. 2: exact Hresult.
        2: unfold normalize64, modulus64; split; apply Z.mod_pos_bound; lia.
        unfold normalize64. set (r_pos := get_word result pos).
        set (P := 2^(64 * Z.of_nat pos)). set (M_R := modulus_words R).
        assert (HMP: modulus64 * P = M_R).
        { unfold M_R, modulus_words, words_bits, P, modulus64.
          rewrite <- Z.pow_add_r by lia. f_equal. subst pos. lia. }
        apply Z_mod_divide_diff;
          [unfold M_R, modulus_words, words_bits; apply Z.pow_nonzero; lia | ].
        pose proof (Z_div_mod_eq_full (r_pos + c_lo) modulus64) as Hdm.
        exists (-((r_pos + c_lo) / modulus64 + to_Z64 c_hi)).
        unfold to_Z64. rewrite <- HMP. nia.
      * (* pos >= R: result unchanged, carry vanishes mod M_R *)
        apply Nat.ltb_ge in H2.
        unfold modulus_words, words_bits.
        replace (64 * Z.of_nat pos)
          with (64 * Z.of_nat R + 64 * (Z.of_nat pos - Z.of_nat R)) by lia.
        rewrite Z.pow_add_r by lia.
        replace (Z.of_nat R * 64) with (64 * Z.of_nat R) by lia.
        set (M_R := 2^(64 * Z.of_nat R)).
        set (excess := 2^(64 * (Z.of_nat pos - Z.of_nat R))).
        replace ((to_Z64 c_hi * modulus64 + to_Z64 c_lo) * (M_R * excess))
          with ((to_Z64 c_hi * modulus64 + to_Z64 c_lo) * excess * M_R) by ring.
        rewrite Z_mod_plus_full. reflexivity.
  - (* Inductive case: xs_tail = x :: rest *)
    cbn [mul_add_line_recur].
    inversion Hxs as [|x' rest' Hx Hrest]; subst x' rest'.
    cbn [length] in HRI.
    destruct (I + J <? R)%nat eqn:HIJ.
    + (* I + J < R *)
      apply Nat.ltb_lt in HIJ.
      destruct (I + J + 2 <? R)%nat eqn:HIJ2.
      * (* Sub-case: I+J+2 < R — full mulx + adc_3 *)
        apply Nat.ltb_lt in HIJ2.
        pose proof (mulx64_correct x y_i ltac:(lia) ltac:(lia)) as Hmulx.
        pose proof (mulx64_hi_bounded x y_i Hx Hyi) as Hhi.
        pose proof (mulx64_lo_bounded x y_i Hx Hyi) as Hlo.
        pose proof (mulx64_hi_le x y_i Hx Hyi) as Hhile.
        set (r := mulx64 x y_i). fold r in Hhi, Hlo, Hhile.
        pose proof (get_word_bounded result (I + J) Hresult ltac:(lia)) as Hgw.
        unfold to_Z64 in Hhi, Hlo, Hhile.
        pose proof (adc_3_correct (hi r) (lo r) (get_word result (I + J))
          c_hi c_lo ltac:(lia) Hlo Hgw Hchi Hclo) as Hadc3.
        pose proof (adc_3_r2_bounded (hi r) (lo r) (get_word result (I + J))
          c_hi c_lo ltac:(lia) Hlo Hgw Hchi Hclo) as Hr2.
        destruct (adc_3 (hi r) (lo r) (get_word result (I + J)) c_hi c_lo)
          as [[c_hi' c_lo'] res_IJ] eqn:Hadc3_eq.
        destruct Hadc3 as [Hadc3_main [Hres_IJ Hclo']].
        rewrite IH.
        2: exact Hrest. 2: exact Hyi. 2: exact Hr2. 2: exact Hclo'.
        2: apply set_word_valid; [exact Hresult | exact Hres_IJ].
        2: rewrite set_word_length; exact Hlen. 2: lia.
        rewrite to_Z_words_set_word
          by (try rewrite set_word_length; lia || assumption).
        set (P := 2^(64 * Z.of_nat (I + J))).
        set (M := modulus64). set (M_R := modulus_words R).
        assert (Hmulx_M: hi r * M + lo r = x * y_i).
        { unfold M, r in Hmulx. cbv zeta in Hmulx. unfold to_Z64 in Hmulx.
          rewrite Z.shiftl_mul_pow2 in Hmulx by lia. fold r in Hmulx.
          change (2^64) with M in Hmulx. lia. }
        replace (Z.of_nat (I + S J)) with (1 + Z.of_nat (I + J)) by lia.
        replace (64 * (1 + Z.of_nat (I + J)))
          with (64 + 64 * Z.of_nat (I + J)) by lia.
        rewrite Z.pow_add_r by lia. fold P. change (2^64) with M.
        cbn [to_Z_words]. f_equal.
        unfold to_Z64 in Hadc3_main, Hmulx_M |- *.
        change (2^64) with M. fold M in Hadc3_main. nia.
      * (* I+J+2 >= R *)
        apply Nat.ltb_ge in HIJ2.
        destruct (I + J + 1 <? R)%nat eqn:HIJ1.
        -- (* Sub-case: I+J+1 < R, I+J+2 >= R — adc_2_full *)
           apply Nat.ltb_lt in HIJ1.
           assert (HIJ_eq: (I + J + 2 = R)%nat) by lia.
           set (lo_val := normalize64 (x * y_i)).
           pose proof (adc_2_full_correct lo_val (get_word result (I + J))
             c_hi c_lo
             ltac:(unfold lo_val, normalize64; split;
               [apply Z.mod_pos_bound; unfold modulus64; lia |
                apply Z.mod_pos_bound; unfold modulus64; lia])
             ltac:(apply get_word_bounded; [assumption | lia])
             Hchi Hclo) as Hadc2.
           destruct (adc_2_full lo_val (get_word result (I + J)) c_hi c_lo)
             as [c_lo' res_IJ] eqn:Hadc2_eq.
           destruct Hadc2 as [Hadc2_main [Hres_IJ Hclo']].
           rewrite IH.
           2: exact Hrest. 2: exact Hyi. 2: unfold modulus64; lia. 2: exact Hclo'.
           2: apply set_word_valid; [exact Hresult | exact Hres_IJ].
           2: rewrite set_word_length; exact Hlen. 2: lia.
           rewrite to_Z_words_set_word by (lia || assumption).
           set (P := 2^(64 * Z.of_nat (I + J))).
           set (M := modulus64). set (M_R := modulus_words R).
           replace (Z.of_nat (I + S J)) with (1 + Z.of_nat (I + J)) by lia.
           replace (64 * (1 + Z.of_nat (I + J)))
             with (64 + 64 * Z.of_nat (I + J)) by lia.
           rewrite Z.pow_add_r by lia. fold P. change (2^64) with M.
           set (S_ := lo_val * M + get_word result (I + J) + c_hi * M + c_lo).
           assert (Hmod_eq: c_lo' * M + res_IJ = S_ mod (M * M)).
           { unfold S_, M. exact Hadc2_main. }
           assert (HM2P: M * M * P = M_R).
           { unfold M_R, modulus_words, words_bits, P, M, modulus64.
             repeat rewrite <- Z.pow_add_r by lia. f_equal. lia. }
           pose proof (Z_div_mod_eq_full S_ (M * M)) as HdmS.
           pose proof (Z_div_mod_eq_full (x * y_i) M) as Hdmx.
           cbn [to_Z_words].
           unfold to_Z64 in Hmod_eq, HdmS, Hdmx |- *.
           unfold lo_val, normalize64, S_, M in Hmod_eq, HdmS, Hdmx |- *.
           fold M in Hmod_eq, HdmS, Hdmx. fold S_ in Hmod_eq, HdmS.
           change (2^64) with M. fold M in HM2P.
           apply Z_mod_divide_diff;
             [unfold M_R, modulus_words, words_bits; apply Z.pow_nonzero; lia | ].
           exists (-(x * y_i / M + S_ / (M * M))).
           assert (Hlo_eq: lo_val = (x * y_i) mod M) by reflexivity.
           rewrite <- HM2P. nia.
        -- (* Sub-case: I+J < R, I+J+1 >= R — last position, I+J = R-1 *)
           apply Nat.ltb_ge in HIJ1.
           assert (HIJ_eq: (I + J = R - 1)%nat) by lia.
           set (result' := set_word result (I + J)
                  (normalize64 (get_word result (I + J) + c_lo))).
           rewrite IH.
           2: exact Hrest. 2: exact Hyi. 2: exact Hchi. 2: exact Hclo.
           2: unfold result'; apply set_word_valid; [exact Hresult|];
              unfold normalize64; apply Z.mod_pos_bound; unfold modulus64; lia.
           2: unfold result'; rewrite set_word_length; exact Hlen. 2: lia.
           set (P := 2^(64 * Z.of_nat (I + J))).
           set (M := modulus64). set (M_R := modulus_words R).
           assert (HMP: M * P = M_R).
           { unfold M_R, modulus_words, words_bits, P, M, modulus64.
             rewrite <- Z.pow_add_r by lia. f_equal. lia. }
           replace (Z.of_nat (I + S J)) with (1 + Z.of_nat (I + J)) by lia.
           replace (64 * (1 + Z.of_nat (I + J)))
             with (64 + 64 * Z.of_nat (I + J)) by lia.
           rewrite Z.pow_add_r by lia. fold P. change (2^64) with M.
           replace (M * P) with M_R by (rewrite <- HMP; ring).
           rewrite Z_mod_plus_full.
           unfold result'.
           rewrite to_Z_words_set_word.
           2: lia. 2: exact Hresult.
           2: unfold normalize64; split;
              [apply Z.mod_pos_bound; unfold modulus64; lia |
               apply Z.mod_pos_bound; unfold modulus64; lia].
           fold P. unfold normalize64.
           set (r_pos := get_word result (I + J)).
           cbn [to_Z_words]. change (2^64) with M. unfold to_Z64.
           fold M.
           pose proof (Z_div_mod_eq_full (r_pos + c_lo) M) as Hdm.
           apply Z_mod_divide_diff;
             [unfold M_R, modulus_words, words_bits; apply Z.pow_nonzero; lia | ].
           exists (-((r_pos + c_lo) / M + (x + M * to_Z_words rest) * y_i + c_hi)).
           rewrite <- HMP. nia.
    + (* I + J >= R: result unchanged *)
      apply Nat.ltb_ge in HIJ.
      cbn [to_Z_words].
      unfold modulus_words, words_bits.
      replace (64 * Z.of_nat (I + J))
        with (64 * Z.of_nat R + 64 * (Z.of_nat (I + J) - Z.of_nat R)) by lia.
      rewrite Z.pow_add_r by lia.
      replace (Z.of_nat R * 64) with (64 * Z.of_nat R) by lia.
      set (M_R := 2^(64 * Z.of_nat R)).
      set (excess := 2^(64 * (Z.of_nat (I + J) - Z.of_nat R))).
      replace (((to_Z64 x + 2 ^ 64 * to_Z_words rest) * to_Z64 y_i * modulus64
         + to_Z64 c_hi * modulus64 + to_Z64 c_lo) * (M_R * excess))
        with (((to_Z64 x + 2 ^ 64 * to_Z_words rest) * to_Z64 y_i * modulus64
               + to_Z64 c_hi * modulus64 + to_Z64 c_lo) * excess * M_R) by ring.
      rewrite Z_mod_plus_full. reflexivity.
Qed.

(** * Level 3: Row-Level Correctness *)

(** ** mul_line *)

(** mul_line preserves result length *)
Lemma mul_line_length : forall R xs y,
  (0 < R)%nat ->
  length (mul_line R xs y) = R.
Proof.
  intros R xs y HR.
  unfold mul_line. destruct xs as [|x0 rest].
  - apply extend_words_length.
  - apply mul_line_recur_length. rewrite set_word_length. apply extend_words_length.
Qed.

(** mul_line produces valid word list *)
Lemma mul_line_valid : forall R xs y,
  words_valid xs ->
  0 <= y < modulus64 ->
  (0 < R)%nat ->
  words_valid (mul_line R xs y).
Proof.
  intros R xs y Hxs Hy HR.
  unfold mul_line. destruct xs as [|x0 rest].
  - apply extend_words_valid.
  - inversion Hxs as [|x0' rest' Hx0 Hrest]; subst.
    pose proof (mulx64_hi_bounded y x0 Hy Hx0) as Hhi.
    pose proof (mulx64_lo_bounded y x0 Hy Hx0) as Hlo.
    apply mul_line_recur_valid; try assumption.
    + apply set_word_valid; [apply extend_words_valid | exact Hlo].
    + rewrite set_word_length. apply extend_words_length.
Qed.

(** mul_line computes result = y * xs (first row, no accumulation).
    More precisely: to_Z_words(result) mod 2^(64*R) = (y * to_Z_words xs) mod 2^(64*R) *)
Lemma mul_line_correct : forall R xs y,
  words_valid xs ->
  0 <= y < modulus64 ->
  (0 < R)%nat ->
  to_Z_words (mul_line R xs y) mod modulus_words R
  = (to_Z64 y * to_Z_words xs) mod modulus_words R.
Proof.
  intros R xs y Hxs Hy HR.
  unfold mul_line.
  destruct xs as [|x0 rest].
  - cbn [to_Z_words]. rewrite Z.mul_0_r.
    rewrite to_Z_extend_words.
    rewrite Z.mod_0_l by (unfold modulus_words, words_bits; apply Z.pow_nonzero; lia).
    reflexivity.
  - inversion Hxs as [|x0' rest' Hx0 Hrest]; subst.
    pose proof (mulx64_hi_bounded y x0 Hy Hx0) as Hhi.
    pose proof (mulx64_lo_bounded y x0 Hy Hx0) as Hlo.
    pose proof (mulx64_correct y x0 ltac:(lia) ltac:(lia)) as Hmulx.
    set (r := mulx64 y x0).
    set (result' := set_word (extend_words R) 0 (lo r)).
    rewrite mul_line_recur_correct; try assumption.
    + unfold result'.
      rewrite to_Z_words_set_word; [|rewrite extend_words_length; lia
                                   |apply extend_words_valid | exact Hlo].
      rewrite to_Z_extend_words, get_extend_words by lia.
      unfold to_Z64 at 1 2. rewrite Z.mul_0_l, Z.sub_0_r.
      simpl (Z.of_nat _); rewrite Z.add_0_l, Z.pow_0_r, Z.mul_1_r.
      cbn [to_Z_words Z.mul Z.pow_pos Pos.mul].
      unfold to_Z64 in *. rewrite Z.shiftl_mul_pow2 in Hmulx by lia.
      f_equal. subst r.
      lia.
    + unfold result'. apply set_word_valid; [apply extend_words_valid | exact Hlo].
    + unfold result'. rewrite set_word_length. apply extend_words_length.
    + intros j Hj1 Hj2. unfold result'.
      rewrite get_set_word_other by lia. apply get_extend_words. lia.
Qed.

(** ** mul_add_line *)

(** mul_add_line preserves result length *)
Lemma mul_add_line_length : forall I R xs y_i result,
  length result = R ->
  length (mul_add_line I R xs y_i result) = R.
Proof.
  intros I R xs y_i result Hlen.
  unfold mul_add_line. destruct xs as [|x0 rest].
  - exact Hlen.
  - destruct (I + 1 <? R)%nat; apply mul_add_line_recur_length; exact Hlen.
Qed.

(** mul_add_line produces valid word list *)
Lemma mul_add_line_valid : forall I R xs y_i result,
  words_valid xs ->
  0 <= y_i < modulus64 ->
  words_valid result ->
  length result = R ->
  (R <= I + length xs)%nat ->
  words_valid (mul_add_line I R xs y_i result).
Proof.
  intros I R xs y_i result Hxs Hy Hresult Hlen HRI.
  unfold mul_add_line. destruct xs as [|x0 rest].
  - exact Hresult.
  - inversion Hxs as [|x0' rest' Hx0 Hrest]; subst x0' rest'.
    cbn [length] in HRI.
    destruct (I + 1 <? R)%nat eqn:HIR.
    + pose proof (mulx64_hi_bounded x0 y_i Hx0 Hy) as Hhi.
      pose proof (mulx64_lo_bounded x0 y_i Hx0 Hy) as Hlo.
      apply mul_add_line_recur_valid; try assumption; try exact Hhi; try exact Hlo.
      lia.
    + apply mul_add_line_recur_valid; try assumption.
      * unfold modulus64; lia.
      * unfold normalize64. split; [apply Z.mod_pos_bound; unfold modulus64; lia|].
        apply Z.mod_pos_bound. unfold modulus64. lia.
      * lia.
Qed.

(** mul_add_line accumulates one row of partial products:
    to_Z_words(result') mod 2^(64*R)
    = (to_Z_words result + y_i * to_Z_words xs * 2^(64*I)) mod 2^(64*R) *)
Lemma mul_add_line_correct : forall I R xs y_i result,
  words_valid xs ->
  0 <= y_i < modulus64 ->
  words_valid result ->
  length result = R ->
  (0 < R)%nat ->
  (R <= I + length xs)%nat ->
  to_Z_words (mul_add_line I R xs y_i result) mod modulus_words R
  = (to_Z_words result + to_Z64 y_i * to_Z_words xs * 2^(64 * Z.of_nat I))
    mod modulus_words R.
Proof.
  intros I R xs y_i result Hxs Hy Hresult Hlen HR HRI.
  unfold mul_add_line. destruct xs as [|x0 rest].
  - cbn [to_Z_words]. rewrite Z.mul_0_r, Z.mul_0_l, Z.add_0_r. reflexivity.
  - inversion Hxs as [|x0' rest' Hx0 Hrest]; subst x0' rest'.
    cbn [length] in HRI.
    destruct (I + 1 <? R)%nat eqn:HIR.
    + (* I+1 < R: mulx x0 y_i → (hi r, lo r) *)
      apply Nat.ltb_lt in HIR.
      pose proof (mulx64_correct x0 y_i ltac:(lia) ltac:(lia)) as Hmulx.
      pose proof (mulx64_hi_bounded x0 y_i Hx0 Hy) as Hhi.
      pose proof (mulx64_lo_bounded x0 y_i Hx0 Hy) as Hlo.
      set (r := mulx64 x0 y_i).
      rewrite mul_add_line_recur_correct; try assumption.
      * (* hi*M + lo = x0*y_i, so rest*y_i*M + hi*M + lo = rest*y_i*M + x0*y_i *)
        f_equal. cbn [to_Z_words]. unfold to_Z64 in *.
        rewrite Z.shiftl_mul_pow2 in Hmulx by lia.
        replace (Z.of_nat (I + 0)) with (Z.of_nat I) by lia.
        unfold modulus64, r in *. nia.
      * lia.
    + (* I+1 >= R: c_hi = 0, c_lo = normalize64(x0 * y_i) *)
      apply Nat.ltb_ge in HIR.
      rewrite mul_add_line_recur_correct; try assumption.
      * (* rest*y_i*M + (x0*y_i) mod M ≡ (x0 + M*rest)*y_i (mod M_R)
             because (x0*y_i - (x0*y_i) mod M) * P is a multiple of M_R *)
        apply Z_mod_divide_diff.
        { unfold modulus_words, words_bits; apply Z.pow_nonzero; lia. }
        set (P := 2^(64 * Z.of_nat I)).
        assert (HMP: modulus64 * P = modulus_words R * 2^(64 * Z.of_nat (I + 1 - R))).
        { unfold modulus_words, words_bits, P, modulus64.
          repeat rewrite <- Z.pow_add_r by lia. f_equal. lia. }
        replace (Z.of_nat (I + 0)) with (Z.of_nat I) by lia. fold P.
        cbn [to_Z_words]. unfold to_Z64, normalize64.
        pose proof (Z_div_mod_eq_full (x0 * y_i) modulus64) as Hdm.
        exists (-(x0 * y_i / modulus64) * 2^(64 * Z.of_nat (I + 1 - R))).
        assert (Hk: -(x0 * y_i / modulus64) * 2^(64 * Z.of_nat (I + 1 - R))
                      * modulus_words R
                  = -(x0 * y_i / modulus64) * (modulus64 * P))
          by (rewrite HMP; ring).
        rewrite Hk. unfold modulus64 in *. nia.
      * unfold modulus64; lia.
      * unfold normalize64. apply Z.mod_pos_bound. unfold modulus64. lia.
      * lia.
Qed.

(** * Level 2: General Word-List Theorem *)

(** Helper: words_to_uint256 / to_Z_words round-trip *)
Lemma words_to_uint256_Z : forall ws,
  length ws = 4%nat ->
  to_Z256 (words_to_uint256 ws) = to_Z_words ws.
Proof.
  intros ws Hlen.
  destruct ws as [|w0 ws1]; [simpl in Hlen; lia|].
  destruct ws1 as [|w1 ws2]; [simpl in Hlen; lia|].
  destruct ws2 as [|w2 ws3]; [simpl in Hlen; lia|].
  destruct ws3 as [|w3 ws4]; [simpl in Hlen; lia|].
  destruct ws4; [|simpl in Hlen; lia].
  cbn [words_to_uint256 to_Z256 to_Z_words]. unfold to_Z256, to_Z64.
  cbn [v0 v1 v2 v3].
  lia.
Qed.

(** Helper: recursive accumulation preserves length *)
Lemma truncating_mul_runtime_recur_length : forall xs ys result I R,
  length result = R ->
  length (truncating_mul_runtime_recur xs ys result I R) = R.
Proof.
  intros xs. induction ys as [|y rest IH]; intros result I R Hlen.
  - exact Hlen.
  - cbn [truncating_mul_runtime_recur]. apply IH. apply mul_add_line_length. exact Hlen.
Qed.

(** Helper: recursive accumulation preserves validity *)
Lemma truncating_mul_runtime_recur_valid : forall xs ys result I R,
  words_valid xs ->
  words_valid ys ->
  words_valid result ->
  length result = R ->
  (R <= I + length xs)%nat ->
  words_valid (truncating_mul_runtime_recur xs ys result I R).
Proof.
  intros xs. induction ys as [|y rest IH]; intros result I R Hxs Hys Hresult Hlen HRI.
  - exact Hresult.
  - cbn [truncating_mul_runtime_recur].
    inversion Hys as [|y' rest' Hy Hrest]; subst.
    apply IH; try assumption.
    + apply mul_add_line_valid; try assumption. reflexivity.
    + apply mul_add_line_length; reflexivity.
    + lia.
Qed.

(** Helper: truncating_mul_runtime produces length R *)
Lemma truncating_mul_runtime_length : forall xs ys R,
  (0 < R)%nat ->
  length (truncating_mul_runtime xs ys R) = R.
Proof.
  intros xs ys R HR. unfold truncating_mul_runtime.
  destruct ys.
  - apply extend_words_length.
  - apply truncating_mul_runtime_recur_length. apply mul_line_length. exact HR.
Qed.

(** Helper: truncating_mul_runtime produces valid words *)
Lemma truncating_mul_runtime_valid : forall xs ys R,
  words_valid xs ->
  words_valid ys ->
  (0 < R)%nat ->
  (R <= 1 + length xs)%nat ->
  words_valid (truncating_mul_runtime xs ys R).
Proof.
  intros xs ys R Hxs Hys HR HRI. unfold truncating_mul_runtime.
  destruct ys as [|y0 rest].
  - apply extend_words_valid.
  - inversion Hys as [|y0' rest' Hy0 Hrest]; subst.
    apply truncating_mul_runtime_recur_valid; try assumption.
    + apply mul_line_valid; assumption.
    + apply mul_line_length; exact HR.
Qed.

(** Correctness of the recursive accumulation loop *)
Lemma truncating_mul_runtime_recur_correct : forall xs ys_tail result I R,
  words_valid xs ->
  words_valid ys_tail ->
  words_valid result ->
  length result = R ->
  (0 < R)%nat ->
  (length xs <= R)%nat ->
  (R <= I + length xs)%nat ->
  to_Z_words (truncating_mul_runtime_recur xs ys_tail result I R) mod modulus_words R
  = (to_Z_words result
     + to_Z_words xs * to_Z_words ys_tail * 2^(64 * Z.of_nat I))
    mod modulus_words R.
Proof.
  intros xs. induction ys_tail as [|y rest IH];
    intros result I R Hxs Hys Hresult Hlen HR HlenR HRI.
  - (* ys_tail = []: no more rows *)
    cbn [truncating_mul_runtime_recur to_Z_words].
    rewrite Z.mul_0_r, Z.mul_0_l, Z.add_0_r. reflexivity.
  - (* ys_tail = y :: rest *)
    cbn [truncating_mul_runtime_recur].
    inversion Hys as [|y' rest' Hy Hrest_valid]; subst.
    set (R := length result) in *.
    set (result' := mul_add_line I R xs y result).
    rewrite IH.
    2: exact Hxs. 2: exact Hrest_valid.
    2: unfold result'; apply mul_add_line_valid; try assumption; reflexivity.
    2: unfold result'; rewrite mul_add_line_length; reflexivity.
    2: exact HR. 2: exact HlenR. 2: lia.
    pose proof (mul_add_line_correct I R xs y result Hxs Hy Hresult
          ltac:(reflexivity) HR HRI) as Hmal.
    fold result' in Hmal.
    assert (HMR_nz: modulus_words R <> 0)
      by (unfold modulus_words, words_bits; apply Z.pow_nonzero; lia).
    rewrite Z.add_mod with (a := to_Z_words result') by exact HMR_nz.
    rewrite Hmal.
    rewrite <- Z.add_mod by exact HMR_nz.
    f_equal.
    cbn [to_Z_words]. rewrite Nat2Z.inj_succ.
    replace (64 * Z.succ (Z.of_nat I)) with (64 + 64 * Z.of_nat I) by lia.
    rewrite Z.pow_add_r by lia. ring.
Qed.

(** The runtime multiplication computes the truncated product:
    to_Z_words(result) = (to_Z_words xs * to_Z_words ys) mod 2^(64*R) *)
Theorem truncating_mul_runtime_correct : forall xs ys R,
  words_valid xs ->
  words_valid ys ->
  (0 < R)%nat ->
  (length xs <= R)%nat ->
  (R <= 1 + length xs)%nat ->
  to_Z_words (truncating_mul_runtime xs ys R) mod modulus_words R
  = (to_Z_words xs * to_Z_words ys) mod modulus_words R.
Proof.
  intros xs ys R Hxs Hys HR HlenR HRI.
  unfold truncating_mul_runtime.
  destruct ys as [|y0 ys_rest].
  - cbn [to_Z_words]. rewrite Z.mul_0_r.
    rewrite to_Z_extend_words. reflexivity.
  - inversion Hys as [|y0' rest' Hy0 Hys_rest]; subst.
    rewrite truncating_mul_runtime_recur_correct; try assumption.
    + (* Compose mul_line_correct with recur *)
      pose proof (mul_line_correct R xs y0 Hxs Hy0 HR) as Hml.
      set (result := mul_line R xs y0) in Hml |- *.
      rewrite Z.add_mod with (a := to_Z_words result) by
        (unfold modulus_words, words_bits; apply Z.pow_nonzero; lia).
      rewrite Hml.
      rewrite <- Z.add_mod by
        (unfold modulus_words, words_bits; apply Z.pow_nonzero; lia).
      f_equal.
      cbn [to_Z_words]. lia.
    + apply mul_line_valid; assumption.
    + apply mul_line_length; assumption.
Qed.

(** * Level 1: Main 256-bit Theorem *)

Theorem truncating_mul256_runtime_correct : forall x y,
  words_valid (uint256_to_words x) ->
  words_valid (uint256_to_words y) ->
  to_Z256 (truncating_mul256_runtime x y) = (to_Z256 x * to_Z256 y) mod 2^256.
Proof.
  intros x y Hx Hy.
  rewrite (uint256_words_equiv x), (uint256_words_equiv y).
  unfold truncating_mul256_runtime.
  set (xs := uint256_to_words x). set (ys := uint256_to_words y).
  set (result := truncating_mul_runtime xs ys 4).
  (* Round-trip: to_Z256 (words_to_uint256 result) = to_Z_words result *)
  rewrite words_to_uint256_Z
    by (unfold result; apply truncating_mul_runtime_length; lia).
  (* result value is in [0, 2^256), so mod is identity *)
  assert (Hvalid: words_valid result)
    by (unfold result; apply truncating_mul_runtime_valid;
        try assumption; unfold xs, uint256_to_words; simpl; lia).
  pose proof (words_valid_bound result Hvalid) as Hbound.
  replace (length result) with 4%nat in Hbound
      by (unfold result; symmetry; apply truncating_mul_runtime_length; lia).
  rewrite <- Z.mod_small with (b := 2^256) at 1 by exact Hbound.
  (* Apply truncating_mul_runtime_correct *)
  pose proof (truncating_mul_runtime_correct xs ys 4 Hx Hy ltac:(lia)
    ltac:(unfold xs, uint256_to_words; simpl; lia)
    ltac:(unfold xs, uint256_to_words; simpl; lia)) as Hcorrect.
  replace (modulus_words 4) with (2^256) in Hbound, Hcorrect
    by (unfold modulus_words, words_bits; lia).
  rewrite <- Hcorrect.
  f_equal.
Qed.
