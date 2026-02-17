(** * Long Division Model (single-word divisor)

    Models the C++ long_div function which divides an M-word number
    by a single-word divisor. The control flow is identical for both
    constexpr and runtime paths; only the leaf div64 primitive differs.

    This file contains only definitions. Proofs are in DivisionProofs.v.

    C++ reference (uint256.hpp, long_div):
      constexpr uint64_t long_div(size_t m, uint64_t const *u, uint64_t v, uint64_t *quot) {
          auto r = div(0, u[m - 1], v);
          quot[m - 1] = r.quot;
          for (auto i = static_cast<intmax_t>(m) - 2; i >= 0; i--) {
              r = div(r.rem, u[i], v);
              quot[i] = r.quot;
          }
          return r.rem;
      }
*)

From Stdlib Require Import ZArith Lia List.
From Uint256 Require Import Primitives Words.
Import ListNotations.
Open Scope Z_scope.

(** Result of long division *)
Record long_div_result := mk_long_div_result {
  ld_quot : words;
  ld_rem : uint64
}.

(** Process words from most significant to least significant.
    Input: list in MSW-first order (i.e., rev of little-endian).
    Each step divides (rem * 2^64 + u) by v, passing remainder forward. *)
Fixpoint long_div_fold (us : words) (v : uint64) (rem : uint64) : long_div_result :=
  match us with
  | [] => mk_long_div_result [] rem
  | u :: rest =>
      let r := div64 rem u v in
      let rec_result := long_div_fold rest v (rem64 r) in
      mk_long_div_result (quot64 r :: ld_quot rec_result) (ld_rem rec_result)
  end.

(** long_div: divide word list by single word.
    Input is little-endian, so we reverse to process MSW first,
    then reverse quotient back to little-endian. *)
Definition long_div (us : words) (v : uint64) : long_div_result :=
  let r := long_div_fold (rev us) v 0 in
  mk_long_div_result (rev (ld_quot r)) (ld_rem r).
