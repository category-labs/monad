Require Import QArith.
Require Import Lens.Elpi.Elpi.
Require Import bluerock.lang.cpp.cpp.
Require Import stdpp.gmap.
Require Import monad.proofs.misc.
Require Import monad.proofs.evmopsem.
Print block.step.
Print evm.network.
Import linearity.
Require Import monad.asts.exb.
Require Export bluerock.auto.cpp.spec.

Require Import monad.proofs.libspecs.
Import cQp_compat.
#[local] Open Scope lens_scope.

#[local] Open Scope Z_scope.
(*
Require Import EVMOpSem.evmfull. *)
Import cancelable_invariants.
Require Import List.
Require Import bluerock.auto.cpp.
Require Import bluerock.auto.cpp.specs.
Require Import monad.proofs.exec_specs.

Record Proposal :=
  {
    roundNumber: N;
    proposedBlock: Block
  }.

Inductive ActiveBlock :=
| finalized (block_number: N)
| proposalForNextBlock (block_number: N) (round_number:N).


Record DbModel : Type :=
  {
    finalizedBlocks: list (Block * evm.GlobalState); (* dbAuthR asserts that the indices of these blocks must be contiguous. head is the latest finalized block. snd component is the state JUST AFTER executing the block *)
    nextBlockProposals:  list (Proposal * evm.GlobalState);
    activeBlock: ActiveBlock; (* changed by set_block_and_round. dbAuthR asserts that the block number is  *)
    cinvGloc: gname;
  }.

#[only(lens)] derive DbModel.

Section with_Sigma.
  Context `{Sigma:cpp_logic} {CU: genv} {hh: HasOwn mpredI fracR}. (* some standard assumptions about the c++ logic *)

  Context  {MODd : exb.module ⊧ CU}.
  Compute (find_struct "monad::Db" module).

  
  Definition bnumber (b: Block) : N := number (header b).
  Open Scope Z_scope.
  Fixpoint contiguousBlocksStartingFrom (oblockIndex: option Z) (l: list (Block * evm.GlobalState)) : Prop :=
    match l with
    | [] => True
    | h::tl => match oblockIndex with
               | Some blockIndex => Z.to_N blockIndex = bnumber (fst h) /\ contiguousBlocksStartingFrom (Some (blockIndex - 1)) tl
               | None => contiguousBlocksStartingFrom (Some (bnumber (fst h) - 1)) tl
               end
                 
    end.

  Definition validActiveBlock  (m: DbModel) : Prop :=
    match activeBlock m with
    | finalized blockNum =>
        match head (finalizedBlocks m), last (finalizedBlocks m) with
        | Some lastFinBlock, Some oldestFinalizedBlockInDb =>
            (bnumber (fst oldestFinalizedBlockInDb) <= blockNum <= bnumber (fst lastFinBlock))%Z
        | _ , _ => False (* this case hits when the [(finalizedBlocks m)] is empty *)
        end
    | proposalForNextBlock blockNum roundNum =>
        match head (finalizedBlocks m) with
        | Some lastFinBlock => (Z.of_N blockNum = 1 + bnumber (fst lastFinBlock))
        | None => True (* no block has been finalized yet. TODO: should blockNum be 0 in this case? *)
        end /\ roundNum < lengthZ (nextBlockProposals m)
    end.

  Definition validModel (m: DbModel) : Prop :=
    contiguousBlocksStartingFrom None (finalizedBlocks m)
    /\ validActiveBlock m. (* needs to also say that the evm.GlobalState parts are obtained by executiing EVM semantics of a block on the state at the end of the previous block *)

  Definition dummyEvmState: evm.GlobalState. Proof. Admitted.
  
  Definition stateAfterActiveBlock (m: DbModel) : evm.GlobalState :=
    match activeBlock m with
    | finalized blockNum =>
        match head (finalizedBlocks m) with
        | Some lastFinBlock =>
            let offset := bnumber (fst lastFinBlock) - blockNum in
            nth (Z.to_nat offset) (map snd (finalizedBlocks m)) dummyEvmState
        | _  => dummyEvmState (* validModel rules this case out *)
        end
    | proposalForNextBlock _ roundNum =>
        nth (Z.to_nat roundNum) (map snd (nextBlockProposals m)) dummyEvmState
    end.
  (** contains the auth ownership of monad::mpt::Db in-memory datastructures AND also the on-disk datastructures. there can be only 1 object owning the on-disk data at any given time. full 1 fraction is needed to update the state. this ownership [dbAuthR 1 _] is disjoint from [dbFragR] below. The latter can be used to read the database even when some other thread owns [dbAuthR 1 _]: the actual ownership of the disk/memory lives in a concurrent invariant *)
  Definition dbAuthR (q:Qp) (m: DbModel) : Rep. Proof. Admitted.

  (* when we fill in the definition of dbAuthR, we must ensure the lemmas below are provable *)
  Lemma dbAuthREntails (q:Qp) (m: DbModel) : dbAuthR q m |--  dbAuthR q m ** [| validModel m|].
  Proof. Admitted.
                                                     
  (** Raw db ownersip (the part that is remaining after dbAuthR above), shared with RODb instances. can use this to construct trie_rodb. RPC and statesync server(s) use fractions of this ownership to read the on-disk data *)
  Definition dbFragR  (q:Qp) : mpred. Proof. Admitted.

  cpp.spec "monad::Db::read_storage(const evmc::address&, monad::Incarnation, const evmc::bytes32&)"
    as read_storage_spec_auth with (fun (this:ptr) =>
      \prepost{q preDb} this |-> dbAuthR q preDb
      \arg{addressp} "address" (Vptr addressp)
      \prepost{q address} addressp |-> addressR q address
      \arg{incp} "incarnation" (Vptr incp)
      \prepost{q blockTxInd} incp |-> IncarnationR q blockTxInd
      \arg{keyp} "key" (Vptr keyp)
      \prepost{key:N} keyp |-> bytes32R q key
      \post{retp:ptr} [Vptr retp]  retp |-> bytes32R 1 (exec_specs.lookupStorage (stateAfterActiveBlock preDb) address key blockTxInd)).

  cpp.spec "monad::Db::finalize(unsigned long, unsigned long)"
    as finalize_spec_auth with (fun (this:ptr) =>
      \prepost{q preDb} this |-> dbAuthR q preDb
      \arg{blockNum:N}   "block_number" (Vint blockNum)
      \arg{roundNum:N}   "round_number" (Vint roundNum)
      \post this |-> dbAuthR q (preDb &: _activeBlock .= finalized blockNum)).

End with_Sigma.
