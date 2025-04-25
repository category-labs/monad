Require Import bluerock.auto.cpp.proof.
Require Import bluerock.auto.cpp.tactics4.
Section with_Sigma.
  Context `{Sigma:cpp_logic} {CU: genv}.

Lemma primR_anyR_ex: ∀  (t : type) (q : cQp.t),
    Exists v,  primR t q v ⊢ anyR t q.
Proof using.
  intros.
  go.
Qed.

Lemma uncurry_post_wand (P:mpred) (Qs Q: ptr -> mpred):
  (P -* Forall x, (Qs x-* Q x))
    |-- (Forall x, ((P ** Qs x)-* Q x)).
Proof. Admitted.

Lemma wpl f ρ module
  s Qs Q:
  (Forall v, Qs v -* Q v) **  (wp f ρ s (Kreturn (λ v : ptr, Qs v))) |--
    (wp f ρ s (Kcleanup module [] (Kreturn (λ v : ptr, |> Q v)))).
Proof using. Admitted.

End with_Sigma.

Ltac clearPost :=
  repeat match goal with
    | H: mpred |- _ => try clear H
    | H : ptr-> mpred |- _ => try clear H
    end.


Ltac verify_spec2 :=
  work; (* NOT go as that puts Seq into the continuation as Kseq, making the next rewrite fail *)
  try rewrite uncurry_post_wand; (* TODO: make it work only the hyp of the form -* POST v *)
  rewrite <- wpl;
  eagerUnifyU; (* this does not suffice: see split_spec proof. need to do evar tricks to infer Qs *)
  work;
  name_locals;
  cpp.hints.type.has_type_prop_prep;
  try clearPost.

Ltac verify_spec1 :=
  IPM.perm_left ltac:(fun L n =>
                        match L with 
                        denoteModule ?module  =>
                          iApply (verify_spec_new false false false module with ""%string);
                            [vm_compute; reflexivity|]

                        end
                     ).

Ltac verify_spec :=
  iIntrosDestructs;
  verify_spec1;
  verify_spec2.

Ltac runUntilPost :=
  match goal with
    |- context[Kreturn ?post] => hideFromWork post
  end;
  go;
  unhideAllFromWork;
  repeat rewrite <- primR_tptsto_fuzzyR.

Ltac hideLoc l :=
  IPM.perm_left ltac:(fun t n=>
                        match t with
                        | l |-> ?r => hideFromWork r
                        end

                     ).


Notation cinv := (cinvq (nroot .@@ "::demo2")).
Notation cinvr invId q R:=
  (as_Rep (fun this:ptr => cinv invId q (this |-> R))).
#[global]Opaque coPset_difference. (* delete? already in misc.v make sure that one is global too*)
