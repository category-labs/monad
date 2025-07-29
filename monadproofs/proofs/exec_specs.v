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
From AAC_tactics Require Import AAC.

Require Import monad.proofs.libspecs.
Import cQp_compat.
#[local] Open Scope lens_scope.

#[only(lens)] derive block.block_account.
#[only(lens)] derive AccountM.
Section Map.
  Context {A B : Type} {HDE : EqDecision A}.
  Definition ix (a : A) : (A -> B) -l> B :=
    {| Lens.view := fun m => m a
     ; Lens.over := fun (f : B -> B) m =>
         fun a' => if decide (a = a') then f (m a') else m a' |}.
End Map.

(* delete ? *)
Notation resultn ty :=
                  (Ninst (Nscoped (Nscoped (Nglobal (Nid "boost")) (Nid "outcome_v2")) (Nid "basic_result"))
                   [Atype ty;
                    Atype
                      (Tnamed
                         (Ninst (Nscoped (Nglobal (Nid "system_error2")) (Nid "errored_status_code")) [Atype (Tnamed (Ninst (Nscoped (Nscoped (Nglobal (Nid "system_error2")) (Nid "detail")) (Nid "erased")) [Atype "long"]))]));
                    Atype
                      (Tnamed
                         (Ninst (Nscoped (Nscoped (Nscoped (Nscoped (Nglobal (Nid "boost")) (Nid "outcome_v2")) (Nid "experimental")) (Nid "policy")) (Nid "status_code_throw"))
                            [Atype ty;
                             Atype
                               (Tnamed
                                  (Ninst (Nscoped (Nglobal (Nid "system_error2")) (Nid "errored_status_code"))
                                     [Atype (Tnamed (Ninst (Nscoped (Nscoped (Nglobal (Nid "system_error2")) (Nid "detail")) (Nid "erased")) [Atype "long"]))]));
                             Atype "void"]))]).

  (* ------------------------------------------------------------------------- *)
  (* 1) Bundle fields of AccountSubstate into a record                         *)
  (* ------------------------------------------------------------------------- *)
  Record AccountSubstateModel : Type := {
    asm_destructed     : bool;
    asm_touched        : bool;
    asm_accessed       : bool;
    asm_accessed_keys  : list Corelib.Numbers.BinNums.N
  }.

#[local] Open Scope Z_scope.
(*
Require Import EVMOpSem.evmfull. *)
Import cancelable_invariants.



Record AssumptionExactness :=
  {
    min_balance: option N; (* None means exact validation *)
    nonce_exact: bool;
  }.


Definition  ModelWithPtr (ModelType: Type) : Type := ptr * ModelType.
Definition MapModel K V := list (K * ModelWithPtr V).
(* used both for original and current state *)

Record AssumedPreTxAccountState :=
  {
    preTxState : option AccountM; (* None means the account did not exist when read from BlockState. but the account was referenced, e.g. its balance was read to be 0 *)
    assumExactness: AssumptionExactness;
  }.
    
Record UpdatedAccountState :=
  {
    postTxState: option AccountM; (* None means the account committed suicide *)
    substateModel : AccountSubstateModel;
  }.
    
Record TxAssumptionsAndUpdates :=
  {
    preAssumption: AssumedPreTxAccountState;
    originalLoc: ptr;
    txUpdates : option (ptr*(ptr *UpdatedAccountState)); (* None means, the tx did not make any updates to this account. outer ptr is the location in the map, inner ptr is the location of the PartialAccountState in the VersionStack *)
  }.

Record StateM :=
  {
    relaxedValidation: bool;
    preTxAssumedState: MapModel evm.address AssumedPreTxAccountState;
    newStates: MapModel evm.address (list (ptr*UpdatedAccountState)); (* head is the latest *)
    blockStatePtr: ptr;
    indices: Indices
  }.


Module OneTbbMap. Section with_Sigma.
  Context `{Sigma:cpp_logic} {CU: genv} {hh: HasOwn mpredI fracR}. (* some standard assumptions about the c++ logic *)

  (* TODO: generalize over MapOriginalR and MapCurrentR and specialize with AccountStatR, move that up *)
  Definition Rauth {K V:Type} (tykey tyval: type) (khash: K -> N) {eqd: EqDecision K}
           (krep : Qp -> K -> Rep) (* not sure whether this needs to be fractional *)
           (vrep : Qp -> V -> Rep) (* fraction needed as there can be multiple concrrent readers of the value *)
           (* CFrational vrep *)
           (q: stdpp.numbers.Qp) (* one::tbb::concurrent_map itself is used as a value time (storage delta in StateDelta) so Rauth itself must be fractional. q<1 means can only read. unlike Rfrag, we can depend on the value being m *)
           (m: list (K*V))
    : Rep. Proof. Admitted.
(*  structR (Ninst "oneapi::tbb::concurrent_hash_map" [Atype tykey; Atype tyval]) (1/2). *)

  (* TODO: generalize over MapOriginalR and MapCurrentR and specialize with AccountStatR, move that up *)
  Definition Rfrag {K V:Type} (tykey tyval: type) (khash: K -> N) `{EqDecidable K}
           (krep : K -> Rep)
           (vrep : V -> Rep)
           (q: stdpp.numbers.Qp): Rep. Proof. Admitted.
 (*  structR (Ninst "oneapi::tbb::concurrent_hash_map" [Atype tykey; Atype tyval]) (q/2). *)
  
End with_Sigma. End OneTbbMap.


Section with_Sigma.
  Context `{Sigma:cpp_logic} {CU: genv} {hh: HasOwn mpredI fracR}. (* some standard assumptions about the c++ logic *)

Definition AnkerMapR {K V:Type} (tykey tyval: type) (khash: K -> N) (* {eqd: EqDecision K} *)
           (krep : Qp -> K -> Rep) 
           (vrep : Qp -> V -> Rep) (* fraction needed as there can be multiple concrrent readers of the value *)
           (* CFrational vrep *)
           (q: Qp)
           (m: MapModel K V)
    : Rep. Proof. Admitted.
(*  structR (Ninst "anker::map" [Atype tykey; Atype tyval]) (1/2). (* TODO : fix *) *)
  (* move to libspecs *)

Definition AnkerMapSpineR {K:Type} (tykey tyval: type) (khash: K -> N) {eqd: EqDecision K}
           (krep : Qp -> K -> Rep) 
           (q: Qp)
           (locs : list (K*ptr)) (* listed in iteration order *)
    : Rep. Proof. Admitted.
 (* structR (Ninst "anker::map" [Atype tykey; Atype tyval]) (1/2). (* TODO : fix *) *)


Definition AnkerMapPayloadsR {V:Type} (tykey tyval: type) 
           (vrep : Qp -> V -> Rep) (* fraction needed as there can be multiple concrrent readers of the value *)
           (q: Qp)
           (locs : list (ptr*V)) (* listed in iteration order, but clients dont need to know that *)
    : Rep. Proof. Admitted.
(*  structR (Ninst "anker::map" [Atype tykey; Atype tyval]) (1/2). (* TODO : fix *) *)


Lemma AnkerMapSplit {K V:Type} (tykey tyval: type) (khash: K -> N) {eqd: EqDecision K}
           (krep : Qp -> K -> Rep) 
           (vrep : Qp -> V -> Rep) (* fraction needed as there can be multiple concrrent readers of the value *)
           (* CFrational vrep *)
           (q: Qp)
           (m: MapModel K V) :
  AnkerMapR tykey tyval khash krep vrep q m -|-
    AnkerMapSpineR tykey tyval khash krep q (map (fun p => let '(a,(b,c)) := p in (a,b)) m)
    ** AnkerMapPayloadsR tykey tyval vrep q (map (fun p => let '(a,(b,c)) := p in (b,c)) m).
Proof. Admitted.
  Definition u256R  (q:Qp) (n:N) : Rep. Proof. Admitted.
  Definition u256t : type := (Tnamed (Ninst (Nscoped (Nglobal (Nid "intx")) (Nid "uint")) [Avalue (Eint 256 "unsigned int")])).
  Definition bytes32R (q:Qp) (z:N) : Rep. Proof. Admitted.

  Definition DeltaR {T:Type} (ty: type) (Trep : Qp-> T ->  Rep) (q:Qp) (beforeafter: T * T) : Rep. Proof. Admitted.
  
(* A simplistic layout of the "accessed_storage_" table: *)
  Definition AccessedKeysR (q: stdpp.numbers.Qp)
           (keys: list Corelib.Numbers.BinNums.N)
    : bluerock.lang.cpp.logic.rep_defs.Rep :=
    anyR
      "ankerl::unordered_dense::v4_1_0::detail::table<evmc::bytes32, void, ankerl::unordered_dense::v4_1_0::hash<evmc::bytes32, void>, std::equal_to<evmc::bytes32>, std::allocator<evmc::bytes32>, ankerl::unordered_dense::v4_1_0::bucket_type::standard, 0b>"%cpp_type
      (cQp.mut q).
  
  (* A simplistic layout of the "storage_" and "transient_storage_" tables: *)
  Definition StorageMapR (q: Qp)
             (m: list (N*N)) : Rep :=
    anyR
      "ankerl::unordered_dense::v4_1_0::detail::table<evmc::bytes32, evmc::bytes32, ankerl::unordered_dense::v4_1_0::hash<evmc::bytes32, void>, std::equal_to<evmc::bytes32>, std::allocator<std::pair<evmc::bytes32, evmc::bytes32>>, ankerl::unordered_dense::v4_1_0::bucket_type::standard, 1b>"%cpp_type
      (cQp.mut q).

  (* Compute a 256‐bit program‐length hash as an N *)
  Definition code_hash_of_program
             (pr: monad.EVMOpSem.evm.program)
    : Corelib.Numbers.BinNums.N :=
    Stdlib.ZArith.BinInt.Z.to_N
      (monad.EVMOpSem.evm.program_length pr mod (2 ^ 256)%Z).


  Definition computeCodeMap
    (s : StateM)
    : stdpp.gmap.gmap Corelib.Numbers.BinNums.N (list N) :=
    ∅.  (* TOFIXLATER: fold over s.newStates and extract code from each created account *)

  Definition IncarnationR (q:Qp) (i: Indices): Rep. Proof. Admitted.

  (* ------------------------------------------------------------------------- *)
  (* 2) AccountSubstateR with structR                                          *)
  (* ------------------------------------------------------------------------- *)
  Definition AccountSubstateR
             (q: stdpp.numbers.Qp)
             (m: AccountSubstateModel)
    : bluerock.lang.cpp.logic.rep_defs.Rep :=
    _field "AccountSubstate::destructed_"         |-> boolR (cQp.mut q) m.(asm_destructed)
    ** _field "AccountSubstate::touched_"          |-> boolR (cQp.mut q) m.(asm_touched)
    ** _field "AccountSubstate::accessed_"         |-> boolR (cQp.mut q) m.(asm_accessed)
    ** _field "AccountSubstate::accessed_storage_" |-> AccessedKeysR q m.(asm_accessed_keys)
    ** structR "monad::AccountSubstate"%cpp_name  (cQp.mut q).

  (* ------------------------------------------------------------------------- *)
  (* 3) AccountR with structR                                                   *)
  (* ------------------------------------------------------------------------- *)
  Definition AccountR
             (q: stdpp.numbers.Qp)
             (ac: AccountM) : Rep :=
    let ba := coreAc ac in
    _field "monad::Account::balance"       |-> u256R q (w256_to_N ba.(monad.EVMOpSem.block.block_account_balance))
    ** _field "monad::Account::code_hash"  |-> bytes32R q (code_hash_of_program ba.(monad.EVMOpSem.block.block_account_code))
    ** _field "monad::Account::nonce"      |-> primR "unsigned long" (cQp.mut q) (w256_to_Z ba.(monad.EVMOpSem.block.block_account_nonce))
    ** _field "monad::Account::incarnation"|-> IncarnationR q (incarnation ac)
    ** structR "monad::Account"%cpp_name    (cQp.mut q).

  Definition storageMapOf (p: option AccountM): list (N*N). Proof. Admitted.
  
  (* TODO: make it a notation *)
  Definition AccountStateRcore
             (q: Qp)
             (origp: option AccountM) : Rep :=
    _field "monad::AccountState::account_"
         |-> libspecs.optionR
              "monad::Account"%cpp_type
              (fun ba => AccountR q ba)
              q
              origp
    ** _field "monad::AccountState::storage_"
              |-> StorageMapR q (storageMapOf origp)
   ** (Exists transient_map, _field "monad::AccountState::transient_storage_"
                                          |-> StorageMapR q transient_map)
    ** structR "monad::AccountState"%cpp_name (cQp.mut q).
  
  Definition OriginalAccountStateR
    (q: Qp)
    (os: AssumedPreTxAccountState) : Rep :=
    let asm := assumExactness os in 
    AccountStateRcore q (preTxState os) 
    ** _field "monad::AccountState::validate_exact_nonce_"   |-> boolR (cQp.mut q) (nonce_exact asm)
    (* exact‐balance flag *)
    ** _field "monad::AccountState::validate_exact_balance_" |-> boolR (cQp.mut q)
                                                                    (Corelib.Init.Datatypes.negb
                                                                       (bool_decide (stdpp.option.is_Some (min_balance asm))))
    (* min_balance_ bound *)
    ** _field "monad::AccountState::min_balance_" |->
        match min_balance asm with             
        | Some n => u256R q n
        | None =>
           Exists (nb: N),  u256R q nb
        end
     ** (Exists garbage, _base "monad::AccountState"%cpp_name "monad::AccountSubstate"%cpp_name
                           |-> AccountSubstateR q garbage) (* ideally, this should be removed from the c++ class. substate fields are not relevant for original acount state: relevant only for updated state *)
    (* the struct itself 
     ** structR "monad::AccountState"%cpp_name (cQp.mut q) *).
  
  Definition UpdatedAccountStateR
    (q: Qp)
    (os: UpdatedAccountState) : Rep :=
    AccountStateRcore q (postTxState os) **
      _base "monad::AccountState"%cpp_name "monad::AccountSubstate"%cpp_name
      |-> AccountSubstateR q (substateModel os).

  Definition accountStorageDelta (beforeafter: evm.storage * evm.storage) : list (N * (N * N)). Proof. Admitted.

  Definition pairMap {A B:Type} (f: A -> B) (p : A*A) : B*B := (f (fst p), f (snd p)).

  
  Definition StateDeltaR (q:Qp) (beforeaft:  AccountM * AccountM) : Rep :=
    _field "monad::StateDelta::account" |-> DeltaR "monad::Account" AccountR q beforeaft
    ** _field "monad::StateDelta::storage"
      |-> OneTbbMap.Rauth
           "::evmc::bytes32"
           (Tnamed (Ninst "monad::Delta" [Atype "::evmc::bytes32"]))
           (fun x:N => x)
           bytes32R
           (DeltaR "::evmc::bytes32" bytes32R)
           q
           (accountStorageDelta
              (pairMap (fun x => (block.block_account_storage (coreAc x)))  beforeaft))
    ** structR "monad::StateDelta" q.

  

  Definition globalDelta (beforeAfter: evm.GlobalState * evm.GlobalState) : list (evm.address * (AccountM * AccountM)). Proof. Admitted.
  
  Definition StateDeltasR (q:Qp) (beforeAfter: evm.GlobalState * evm.GlobalState) : Rep :=
    OneTbbMap.Rauth
      "evmc::address"
      "monad::StateDelta"
      (fun a => Z.to_N (word160.word160ToInteger a))
      addressR
      StateDeltaR
      q
      (globalDelta beforeAfter).

  Definition CodeDeltaR (q:Qp) (beforeAfter: evm.GlobalState * evm.GlobalState) : Rep. Proof. Admitted.
    (*
    OneTbbMap.Rauth
      "evmc::address"
      "std::shared_ptr<CodeAnalysis>"
      (fun a => Z.to_N (word160.word160ToInteger a))
      addressR
      StateDeltaR
      q
      (globalDelta beforeAfter).
  *)
End with_Sigma.
Module BlockState. Section with_Sigma.
  Context `{Sigma:cpp_logic} {CU: genv} {hh: HasOwn mpredI fracR}. (* some standard assumptions about the c++ logic *)


  Context (blockPreState: StateOfAccounts). (* BlockState is a type that makes sense in the context of a block and the state before the block  *)
  (** defines how the Coq (mathematical) state of Coq type [StateOfAccounts] is represented as a C++ datastructure in the fields of the BlockState class.
      [blockPreState] is the state at the beginning of the block.  newState
   *)
    

  Record glocs :=
    {
      cmap: gname;
    }.

  Definition Rauth (g: glocs) (newState: StateOfAccounts): Rep.
  Proof using blockPreState. Admitted. (* To be defined later. something like: [_field db_ |-> DbR blockPreState ** _field deltas |-> StateDeltasR blockPreState newState] *)

  Definition Rfrag (q:Qp) (g: glocs): Rep.
  Proof using blockPreState. Admitted.

  (* TODO: move to a proofmisc file and replace by a lemma about just binary splitting *)
  Lemma split_frag {T} q g (l : list T):
    Rfrag q g -|- Rfrag (q/(N_to_Qp (1+ lengthN l))) g ** 
    ([∗ list] _ ∈ l,  (Rfrag (q*/(N_to_Qp (1+ lengthN l))) g)).
  Proof using. Admitted.

  (* TODO: move to a proofmisc file *)
  Lemma split_frag_loopinv {T} q g (l : list T) (i:nat) (prf: i=0):
    Rfrag q g -|- Rfrag (q/(N_to_Qp (1+ lengthN l))) g ** 
    ([∗ list] _ ∈ (drop i l),  (Rfrag (q*/(N_to_Qp (1+ lengthN l))) g)).
  Proof using.
    subst.  autorewrite with syntactic. apply split_frag.
  Qed.

End with_Sigma. End BlockState.


(* Import bluerock.lang.cpp.semantics.values.VALUES_INTF_AXIOM. *)


Open Scope cpp_name.
Section with_Sigma.
  Context `{Sigma:cpp_logic} {CU: genv} {hh: HasOwn mpredI fracR}. (* some standard assumptions about the c++ logic *)

   
  (* defines how [c] is represented in memory as an object of class Chain. this predicate asserts [q] ownership of the object, assuming it can be shared across multiple threads  *)
  Definition ChainR (q: Qp) (c: Chain): Rep. Proof. Admitted.

  Lemma ChainR_split_loopinv {T} q (b: Chain) (l : list T) (i:nat) (p:i=0):
    ChainR q b -|- ChainR (q/(N_to_Qp (1+ lengthN l))) b ** 
    ([∗ list] _ ∈ (drop i l),  (ChainR (q*/(N_to_Qp (1+ lengthN l))) b)).
  Proof using. Admitted.

  Definition tx_nonce tx :=
    (w256_to_N (block.tr_nonce tx)).
  Definition TransactionR (q:Qp) (tx: Transaction) : Rep :=
    structR "monad::Transaction" q **
      _field "monad::Transaction::nonce" |-> ulongR q (tx_nonce tx).

  #[global] Instance learnTrRbase: LearnEq2 TransactionR:= ltac:(solve_learnable).

  Definition BheaderR (q:Qp) (hdr: BlockHeader) : Rep :=
    structR "monad::BlockHeader" q
    ** _field "monad::BlockHeader::base_fee_per_gas" |-> libspecs.optionR u256t (u256R q) q  (base_fee_per_gas hdr)
    ** _field "monad::BlockHeader::number" |-> ulongR q  (number hdr)
    ** _field "monad::BlockHeader::beneficiary" 
         |-> addressR 1 (beneficiary hdr)
    ** _field "monad::BlockHeader::timestamp" |-> primR "unsigned long" q (timestamp hdr).
         
  Definition BlockR (q: Qp) (c: Block): Rep :=
    _field "::monad::Block::transactions" |-> VectorR (Tnamed "::monad::Transaction") (fun t => TransactionR q t) q (transactions c)
    ** _field "::monad::Block::header" |-> BheaderR q (header c)
      ** structR "::monad::Block" q.

  (* TODO: add a Result T type in Coq and change the type of t to Result T *)
  Definition ResultSuccessR {T} (trep: T -> Rep) (t:T): Rep. Proof. Admitted.
  Definition ReceiptR (t: TransactionResult): Rep. Admitted.
  Definition EvmcResultR (t: TransactionResult): Rep. Admitted.
  Definition ResultFailureR: Rep. Proof. Admitted.

  Definition valOfRev (r : Revision) : val := Vint 0. (* TODO: fix *)

  Record BlockHashBuffer :=
    { fullHistory: list N;
      startIndex: N}.

  Definition lastIndex (b: BlockHashBuffer) : N := startIndex b + lengthN (fullHistory b).

  (* move to utils
  Definition rotate_list {A} (r : Z) (elems : list A) : list A :=
    let sz : Z := length elems in
    let split_count : nat := Z.to_nat $ r `mod` length elems in
    drop split_count elems ++ take split_count elems.
*)  
  Definition BlockHashBufferR (q:Qp) (m: BlockHashBuffer) : Rep :=
    _field "monad::n_" |-> u64R q (lastIndex m).
    (* ** _field "monad::b_" |-> arrayR ... (rotate_list ) *)
  Lemma bhb_split_sn {T} q (b: BlockHashBuffer) (l : list T):
    BlockHashBufferR q b -|- BlockHashBufferR (q/(N_to_Qp (1+ lengthN l))) b ** 
    ([∗ list] _ ∈ l,  (BlockHashBufferR (q*/(N_to_Qp (1+ lengthN l))) b)).
  Proof using. Admitted.

  Lemma bhb_splitl_loopinv {T} q (b: BlockHashBuffer) (l : list T) (i:nat) (p:i=0):
    BlockHashBufferR q b -|- BlockHashBufferR (q/(N_to_Qp (1+ lengthN l))) b ** 
    ([∗ list] _ ∈ (drop i l),  (BlockHashBufferR (q*/(N_to_Qp (1+ lengthN l))) b)).
  Proof using.
    intros. subst. autorewrite with syntactic.
    apply bhb_split_sn.
  Qed.
  
  Lemma header_split_loopinv {T} q (b: BlockHeader) (l : list T) (i:nat) (p:i=0):
    BheaderR q b -|- BheaderR (q/(N_to_Qp (1+ lengthN l))) b ** 
    ([∗ list] _ ∈ (drop i l),  (BheaderR (q*/(N_to_Qp (1+ lengthN l))) b)).
  Proof using. Admitted.


                   
  Definition execute_block_simpler : WpSpec mpredI val val :=
    \arg{chainp :ptr} "chain" (Vptr chainp)
    \prepost{(qchain:Qp) (chain: Chain)} chainp |-> ChainR qchain chain
    \arg{blockp: ptr} "block" (Vptr blockp)
    \prepost{qb (block: Block)} blockp |-> BlockR qb block
    \arg{(sendersp: ptr) (qs: Qp)} "senders" (Vptr sendersp)
    \prepost sendersp |-> VectorR (Tnamed "::evmc::address") (addressR qs) qs (map sender (transactions block))
    \arg{block_statep: ptr} "block_state" (Vptr block_statep)
    \pre{(preBlockState: StateOfAccounts) g qf}
       block_statep |-> BlockState.Rauth preBlockState g preBlockState
    \prepost block_statep |-> BlockState.Rfrag preBlockState qf g
    \arg{block_hash_bufferp: ptr} "block_hash_buffer" (Vptr block_hash_bufferp)
    \prepost{buf qbuf} block_hash_bufferp |-> BlockHashBufferR qbuf buf
    \arg{priority_poolp: ptr} "priority_pool" (Vptr priority_poolp)
    \prepost{priority_pool: PriorityPool} priority_poolp |-> PriorityPoolR 1 priority_pool (* TODO: write a spec of priority_pool.submit() *)
    \post{retp}[Vptr retp]
      let (actual_final_state, receipts) := stateAfterBlock block preBlockState in
      retp |-> VectorR (Tnamed "::monad::Receipt") ReceiptR 1 receipts
        ** block_statep |-> BlockState.Rauth preBlockState g actual_final_state.
  (* unproven spec of execute_impl2_specg assumes exec_imp2 never fails. need to add conditions *)


  Definition execute_block_spec_fixed : WpSpec mpredI val val :=
    \arg{chainp :ptr} "chain" (Vptr chainp)
    \prepost{(qchain:Qp) (chain: Chain)} chainp |-> ChainR qchain chain
    \arg{blockp: ptr} "block" (Vptr blockp)
    \prepost{qb (block: Block)} blockp |-> BlockR qb block
    \arg{block_statep: ptr} "block_state" (Vptr block_statep)
    \pre{(preBlockState: StateOfAccounts) g qf}
       block_statep |-> BlockState.Rauth preBlockState g preBlockState
    \prepost block_statep |-> BlockState.Rfrag preBlockState qf g
    \arg{block_hash_bufferp: ptr} "block_hash_buffer" (Vptr block_hash_bufferp)
    \prepost{buf qbuf} block_hash_bufferp |-> BlockHashBufferR qbuf buf
    \arg{priority_poolp: ptr} "priority_pool" (Vptr priority_poolp)
    \prepost{priority_pool: PriorityPool} priority_poolp |-> PriorityPoolR 1 priority_pool 
    \post{retp}[Vptr retp]
    
       match stateAfterBlockV block preBlockState with
       | Some (actual_final_state, results) =>
           retp |-> ResultSuccessR (fun r =>VectorR (Tnamed "::monad::Receipt") ReceiptR 1 r) results
           ** block_statep |-> BlockState.Rauth preBlockState g actual_final_state
       | None =>
          (* [| ¬ txsFeesUB preBlockState (transactions block) |]  this conjunct can be derived as a lemma about stateAfterBlockV *)
           retp |-> ResultFailureR
           ** Exists garbage, block_statep |-> BlockState.Rauth preBlockState g garbage
       end. 


Import namemap.
Import translation_unit.
Require Import List.
Import bytestring_core.
Require Import bluerock.auto.cpp.
Require Import bluerock.auto.cpp.specs.

Eval vm_compute in (firstEntryName (findBodyOfFnNamed2 exb.module (isFunctionNamed2 "execute_block"))).


Context  {MODd : exb.module ⊧ CU}.
  cpp.spec (Ninst
              "monad::execute_block(const monad::Chain&, monad::Block&, const std::vector<evmc::address, std::allocator<evmc::address>>&, monad::BlockState&, const monad::BlockHashBuffer&, monad::fiber::PriorityPool&)"
              [Avalue (Eint 11 "enum evmc_revision")]) as exbb_spec with (execute_block_simpler).


  
  cpp.spec 
  "monad::reset_promises(unsigned long)" as reset_promises with
      ( \with (Transaction: Type)
        \arg{transactions: list Transaction} "n" (Vn (lengthN transactions))
       \pre{newPromisedResource}
           _global "monad::promises" |-> parrayR (Tnamed "boost::fibers::promise<void>") (fun i t => PromiseUnusableR) transactions
       \post Exists prIds, _global "monad::promises" |-> parrayR (Tnamed "boost::fibers::promise<void>") (fun i t => PromiseR (prIds i) (newPromisedResource i t)) transactions).

  (* TODO: this is now the spec of recover_senders, almost.
cpp.spec
  "monad::compute_senders(const monad::Block&, monad::fiber::PriorityPool&)"
  as compute_senders
  with (
    \arg{blockp: ptr} "block" (Vref blockp)
    \prepost{qb (block: Block)} blockp |-> BlockR qb block
    \arg{priority_poolp: ptr} "priority_pool" (Vref priority_poolp)
    \prepost{priority_pool: PriorityPool} priority_poolp |-> PriorityPoolR 1 priority_pool
    \prepost
        _global "monad::promises" |->
          parrayR
            (Tnamed "boost::fibers::promise<void>")
            (fun i t => PromiseUnusableR)
            (transactions block)
    \pre Exists garbage,
        _global "monad::senders" |->
          arrayR
            (Tnamed "std::optional<evmc::address>")
            (fun t=> optionAddressR 1 (garbage t))
            (transactions block)
    \post _global "monad::senders" |->
          arrayR
            (Tnamed "std::optional<evmc::address>")
            (fun t=> optionAddressR 1 (Some (sender t)))
            (transactions block)).
*)

Definition resultT := Tnamed (resultn "monad::ExecutionResult").
Definition ExecutionResultR (tr: TransactionResult): Rep. Proof. Admitted.

Definition oResultT := (Tnamed (Ninst "std::optional" [Atype resultT])).

cpp.spec (Ninst "monad::execute_transactions(const monad::Block&, monad::fiber::PriorityPool&, const monad::Chain&, const std::vector<evmc::address, std::allocator<evmc::address>>&, const monad::BlockHashBuffer&, monad::BlockState &)" [Avalue (Eint 11 "enum evmc_revision")]) as exect with (
    \arg{blockp: ptr} "block" (Vref blockp)
    \prepost{qb (block: Block)} blockp |-> BlockR qb block
    \pre [| lengthN (transactions block) < 2^64 - 1 |]%N
    \arg{priority_poolp: ptr} "priority_pool" (Vref priority_poolp)
    \prepost{priority_pool: PriorityPool} priority_poolp |-> PriorityPoolR 1 priority_pool
    \arg{chainp :ptr} "chain" (Vref chainp)
    \prepost{(qchain:Qp) (chain: Chain)} chainp |-> ChainR qchain chain
    \arg{(sendersp: ptr) (qs: Qp)} "senders" (Vptr sendersp)
    \prepost sendersp |-> VectorR (Tnamed "::evmc::address") (addressR qs) qs (map sender (transactions block))
    \arg{block_hash_bufferp: ptr} "block_hash_buffer" (Vref block_hash_bufferp)
    \prepost{buf qbuf} block_hash_bufferp |-> BlockHashBufferR qbuf buf
    \arg{block_statep: ptr} "block_state" (Vref block_statep)
    \pre{(preBlockState: StateOfAccounts) g qf}
       block_statep |-> BlockState.Rauth preBlockState g preBlockState
    \prepost block_statep |-> BlockState.Rfrag preBlockState qf g
    \prepost
        _global "monad::promises" |->
          parrayR
            (Tnamed "boost::fibers::promise<void>")
            (fun i t => PromiseUnusableR)
            ((map (fun _ => ()) (transactions block))++[()])
    \pre Exists garbage,
        _global "monad::results" |->
          arrayR
            oResultT
            (fun t=> libspecs.optionR resultT (ResultSuccessR ExecutionResultR) 1 (garbage t))
            (transactions block)
   \prepost{qs} _global "monad::senders" |->
          arrayR
            (Tnamed "std::optional<evmc::address>")
            (fun t=> optionAddressR qs (Some (sender t)))
            (transactions block)
   \post
      let (actual_final_state, receipts) := stateAfterTransactions (header block) preBlockState (transactions block) in
      _global "monad::results" |-> arrayR oResultT (fun r => libspecs.optionR resultT (ResultSuccessR ExecutionResultR) 1 (Some r)) receipts
      ** block_statep |-> BlockState.Rauth preBlockState g actual_final_state

    ).
    
    (* \pre assumes that the input is a valid transaction encoding (sender computation will not fail) *)
    cpp.spec "monad::recover_sender(const monad::Transaction&)"  as recover_sender with
        (
    \arg{trp: ptr} "tr" (Vref trp)
    \prepost{qt (tr: Transaction)} trp |-> TransactionR qt tr
    \post{retp} [Vptr retp] retp |-> optionAddressR 1 (Some (sender tr))).

(*
    cpp.spec (fork_task_nameg "monad::compute_senders(const monad::Block&, monad::fiber::PriorityPool&)::@0") as fork_task with (forkTaskSpec "monad::compute_senders(const monad::Block&, monad::fiber::PriorityPool&)::@0").
 *)
    
    (* todo: generalize over the template arg *)
cpp.spec 
  "std::vector<monad::Transaction, std::allocator<monad::Transaction>>::operator[](unsigned long) const" as vector_op_monad with (vector_opg "monad::Transaction").


(*
  erewrite sizeof.size_of_compat;[| eauto; fail| vm_compute; reflexivity].
*)
  
  Definition execute_transaction_spec : WpSpec mpredI val val :=
    \arg{chainp :ptr} "chain" (Vref chainp)
    \prepost{(qchain:Qp) (chain: Chain)} chainp |-> ChainR qchain chain
    \arg{i:nat} "i" (Vnat i)
    \pre [| N.of_nat i < 2^64 - 1 |]%N (* we do i+1 to make the incarnation *)
    \arg{txp} "tx" (Vref txp)
    \prepost{qtx t} txp |-> TransactionR qtx t
    \arg{senderp} "sender" (Vref senderp)
    \prepost{qs} senderp |-> addressR qs (sender t)
    \arg{hdrp: ptr} "hdr" (Vref hdrp)
    \prepost{qh header} hdrp |-> BheaderR qh header
    \arg{block_hash_bufferp: ptr} "block_hash_buffer" (Vref block_hash_bufferp)
    \arg{block_statep: ptr} "block_state" (Vref block_statep)
    \prepost{g qf preBlockState} block_statep |-> BlockState.Rfrag preBlockState qf g
    \arg{prevp: ptr} "prev" (Vref prevp)
    \pre{(prg: gname) (prevTxGlobalState: StateOfAccounts) (OtherPromisedResources:mpred)}
        prevp |-> PromiseConsumerR prg (OtherPromisedResources ** block_statep |-> BlockState.Rauth preBlockState g prevTxGlobalState)
    \post{retp}[Vptr retp] OtherPromisedResources ** prevp |-> PromiseUnusableR **
      let '(finalState, result) := stateAfterTransaction header i prevTxGlobalState t in
       retp |-> ResultSuccessR ExecutionResultR result
         ** block_statep |->  BlockState.Rauth preBlockState g finalState.

  Compute (Nscoped (Nglobal (Nid "monad"))
                (Nfunction function_qualifiers.N ("execute")
                   [Tref (Tconst (Tnamed (Nscoped (Nglobal (Nid "monad")) (Nid "Chain")))); "unsigned long"%cpp_type; Tref (Tconst (Tnamed (Nscoped (Nglobal (Nid "monad")) (Nid "Transaction"))));
                    Tref (Tconst (Tnamed (Ninst (Nscoped (Nglobal (Nid "std")) (Nid "optional")) [Atype (Tnamed (Nscoped (Nglobal (Nid "evmc")) (Nid "address")))])));
                    Tref (Tconst (Tnamed (Nscoped (Nglobal (Nid "monad")) (Nid "BlockHeader")))); Tref (Tconst (Tnamed (Nscoped (Nglobal (Nid "monad")) (Nid "BlockHashBuffer"))));
                    Tref (Tnamed (Nscoped (Nglobal (Nid "monad")) (Nid "BlockState"))); Tref (Tnamed (Ninst (Nscoped (Nscoped (Nglobal (Nid "boost")) (Nid "fibers")) (Nid "promise")) [Atype "void"]))])).
cpp.spec ((Ninst
             "monad::execute(const monad::Chain&, unsigned long, const monad::Transaction&, const evmc::address&, const monad::BlockHeader&, const monad::BlockHashBuffer&, monad::BlockState&, boost::fibers::promise<void>&)"
             [Avalue (Eint 11 (Tenum (Nglobal (Nid "evmc_revision"))))])) as ext1 with (execute_transaction_spec).

Definition destr_res {T} ty (tyR: T-> Rep):=
λ {thread_info : biIndex} {_Σ : gFunctors} {Sigma : cpp_logic thread_info _Σ} {CU : genv},
  specify
    {|
      info_name :=
        Nscoped
          (resultn ty)
          (Ndtor);
      info_type :=
        tDtor
          (resultn ty)
    |} (λ this : ptr, \pre{res} this |-> ResultSuccessR tyR res
                        \post    emp).
#[global] Instance : LearnEq2 ChainR:= ltac:(solve_learnable).
#[global] Instance : LearnEq3 BlockState.Rfrag := ltac:(solve_learnable).
#[global] Instance : LearnEq2 BheaderR := ltac:(solve_learnable).
#[global] Instance rrr {T}: LearnEq2 (@ResultSuccessR T) := ltac:(solve_learnable).
#[global] Instance : LearnEq2 PromiseConsumerR:= ltac:(solve_learnable).

End with_Sigma.


Require Import monad.asts.ext.
Require Import Lens.Lens.
Section with_Sigma.
  Context `{Sigma:cpp_logic} {CU: genv} {hh: HasOwn mpredI fracR}.
  Context  {MODd : ext.module ⊧ CU}.
  
  cpp.spec (Nscoped (Nglobal (Nid "monad")) (Nfunction function_qualifiers.N ("get_chain_id") [Tref (Tconst (Tnamed (Nscoped (Nglobal (Nid "monad")) (Nid "Chain"))))]))
    as get_chain_id with(
      \arg{chainp} "" (Vref chainp)
      \prepost{chain q} chainp |-> ChainR q chain
      \post{retp} [Vptr retp] (retp |-> u256R 1 (chainid chain))).

  Import evm.

      

  Definition addressToN (a: address) : N. Proof. Admitted.
Definition MapOriginalR
           (q: stdpp.numbers.Qp)
           (m: MapModel 
                  evm.address
                  AssumedPreTxAccountState)
  : Rep :=
  AnkerMapR "evmc::address" "monad::OriginalAccountState" 
           addressToN
           addressR
           OriginalAccountStateR
           q
           m.


Definition VersionStackSpineR (cppType: type) (q:Qp) (lt:list ptr): Rep. Proof. Admitted.

Definition VersionStackR {ElemType} (cppType: type) (elemRep: Qp -> ElemType -> Rep) (q:Qp) (lt:list (ptr*ElemType)): Rep :=
  VersionStackSpineR cppType q (map fst lt) ** pureR ([∗ list] p ∈ lt, let '(loc, val) := p in  (loc:ptr) |-> elemRep q val).

Definition MapCurrentR
           (q: stdpp.numbers.Qp)
           (m: MapModel address (list (ptr* UpdatedAccountState)))
  : Rep :=
  AnkerMapR "evmc::address" "monad::VersionStack<monad::AccountState>" 
           addressToN
           addressR
           (VersionStackR "monad::AccountState" UpdatedAccountStateR)
           q
           m.

(*
structR
    "ankerl::unordered_dense::v4_1_0::detail::table<evmc::address, monad::VersionStack<monad::AccountState>, ankerl::unordered_dense::v4_1_0::hash<evmc::address, void>, std::equal_to<evmc::address>, std::allocator<std::pair<evmc::address, monad::VersionStack<monad::AccountState>>>, ankerl::unordered_dense::v4_1_0::bucket_type::standard, 1b>"
    (cQp.mut q).
*)

(** TODO: fix: add the actual logs **)
Definition LogsR (q: stdpp.numbers.Qp) : Rep :=
  structR
    "monad::VersionStack<std::vector<monad::Receipt::Log, std::allocator<monad::Receipt::Log>>>"
    (cQp.mut q).

(** 5) Rep for monad::State::code_ (table<bytes32,shared_ptr<CodeAnalysis>>) **)
Definition CodeMapR
           (q: stdpp.numbers.Qp)
           (cm: stdpp.gmap.gmap Corelib.Numbers.BinNums.N (* bytes32 as N *)
                             (list N)) 
  : Rep. Proof. Admitted.
(*
  structR
    "ankerl::unordered_dense::v4_1_0::detail::table<evmc::bytes32, std::shared_ptr<evmone::baseline::CodeAnalysis>, ankerl::unordered_dense::v4_1_0::hash<evmc::bytes32, void>, std::equal_to<evmc::bytes32>, std::allocator<std::pair<evmc::bytes32, std::shared_ptr<evmone::baseline::CodeAnalysis>>>, ankerl::unordered_dense::v4_1_0::bucket_type::standard, 1b>"
    (cQp.mut q). *)

(** Helper to extract the newly‐deployed code map from the State model **)

(** Now lay out StateR.  We *no longer* re‐open the section here. **)
Definition StateR (s: StateM) : Rep :=
   _field "monad::State::block_state_" |-> ptrR<"monad::BlockState"> 1$m (blockStatePtr s) ∗
   _field "monad::State::incarnation_" |-> IncarnationR 1$m%cQp (indices s) ∗
   _field "monad::State::original_" |-> MapOriginalR 1$m%cQp (preTxAssumedState s) ∗
   _field "monad::State::current_" |-> MapCurrentR 1$m%cQp (newStates s) ∗
   _field "monad::State::logs_" |-> LogsR 1$m%cQp ∗ (* TOFIX: add a model arg to LogsR *)
   _field "monad::State::code_" |-> CodeMapR 1$m%cQp (computeCodeMap s) ∗
   _field "monad::State::version_" |-> uintR 1$m 0 ∗
   _field "monad::State::relaxed_validation_" |-> boolR 1$m (relaxedValidation s) ∗
   structR "monad::State" 1$m.  
  

  Definition nullifyBalNonceStorage (e: AccountM) : AccountM. Proof. Admitted.
  (*    := {[ e with evm.account_balance := 0, evm.account_nonce:=0 ]}. *)
  
  (*
  Definition preImpl2 (blockStatePtr: ptr) (senderAddr: evm.address) (sender: account_state): StateM:=
    {|
      blockStatePtr:= blockStatePtr;
      newStates:= ∅;
      original := <[senderAddr := sender]>∅;
    |}. *)
(*
  Definition EvmcResultR (r: TransactionResult): Rep. Proof. Admitted. *)

  Open Scope Z_scope.

  Definition zbvfun (fz: Z -> Z) (w: keccak.w256): keccak.w256:=
    let wnz := fz (w256_to_Z w) in
    Z_to_w256 wnz.
    
   
  Definition zbvlens {A:Type} (l: Lens A A keccak.w256 keccak.w256): Lens A A Z Z :=
    {| view := λ a : A, w256_to_Z (a .^ l);
      over := λ (fz : Z → Z) (a : A), (l %= zbvfun fz) a |}.
  Definition _balance : Lens AccountM AccountM Z Z (* TODO: Z -> N *):=
    zbvlens (_coreAc .@ _block_account_balance).
  Definition _nonce : Lens AccountM evm.account_state Z Z:=
    zbvlens (_coreAc .@ _block_account_nonce).

  Definition _storage (key: Z): Lens AccountM evm.account_state Z Z:=
    zbvlens (_coreAc .@ _block_account_storage .@ (ix (Z_to_w256 key))).
  
  Definition isNone {T} (a: option T):= negb (isSome a).
  Definition min_balanceN (a: AssumptionExactness) : N:=
    match min_balance a with
    | Some f => f
    | None => 0
    end.

  Global Instance lkk {K V} `{Countable K}:  Lookup K  (ModelWithPtr V) (MapModel K V) := fun k m =>
     (((list_to_map m):(gmap K (ModelWithPtr V))) !! k).

  Definition assumptionAndUpdateOfAddr (s: StateM) (a: evm.address): option TxAssumptionsAndUpdates :=
    match preTxAssumedState s !! a  with
      | None => None
      | Some p => Some
          {|
            preAssumption := snd p;
            originalLoc := fst p;
            txUpdates :=  ((newStates s) !! a) ≫= (fun a => match head (snd a) with
                                                            | None => None
                                                            | Some (loc, upd) => Some (fst a, (loc, upd))
                                                            end
                                                  )
          |}
    end.

  
  Definition satAccountNonStorageAssumptions (relaxedValidation: bool) (a: option TxAssumptionsAndUpdates) (actualPreTxAcState: option AccountM) : Prop :=
      match option_map preAssumption a  with
      | Some assumedPre =>
          let assumEx := assumExactness assumedPre in
          match preTxState assumedPre, actualPreTxAcState  with
          | Some cs, Some csActual =>
             (if (negb relaxedValidation || isNone (min_balance assumEx))
              then cs .^ _balance = csActual .^ _balance
              else (min_balanceN assumEx <= (csActual) .^ _balance))
             /\ (if (negb relaxedValidation || nonce_exact assumEx)
                 then cs .^ _nonce = (csActual).^ _nonce
                 else True)
          | None, None => True
          | _, _ => False
          end
      | None  => True
      end.

  Definition satAccountStrageAssumptions (relaxedValidation: bool) (a: option TxAssumptionsAndUpdates) (actualPreTxAcState: option AccountM) : Prop :=
      match option_map preAssumption a  with
      | Some assumedPreState =>
          let assumEx := assumExactness assumedPreState in
          match preTxState assumedPreState, actualPreTxAcState  with
          | Some cs, Some csActual =>
             (forall storageKey: N, storageKey ∈ relevantKeys cs
                                       -> csActual .^ _storage storageKey = cs .^ _storage storageKey)
          | None, None => True
          | _, _ => False
          end
      | None  => True
      end.
  
  
  Definition satAccountAssumptions (relaxedValidation: bool) (a: option TxAssumptionsAndUpdates) (actualPreTxAcState: option AccountM) : Prop :=
    satAccountNonStorageAssumptions relaxedValidation a actualPreTxAcState /\  satAccountStrageAssumptions relaxedValidation a actualPreTxAcState.
  
  Definition satisfiesAssumptions (a: StateM) (preTxState: StateOfAccounts) : Prop :=
    forall acAddr: address,
      satAccountAssumptions (relaxedValidation a) (assumptionAndUpdateOfAddr a acAddr) (preTxState !! acAddr).

  Definition validAU (relaxedValidation: bool) (a: option TxAssumptionsAndUpdates) : Prop :=
    match option_map preAssumption a  with
    | None  => True
    | Some assumedPreState =>
          let assumEx := assumExactness assumedPreState in
        match preTxState assumedPreState  with
        | None => True
        | Some cs => 
            if (relaxedValidation && isSome (min_balance assumEx))
            then (min_balanceN assumEx <= cs .^ _balance) else True
        end
    end. (* TODO: add more conditions, e.g. about the updates *)
      
  Definition validStateM (a: StateM) : Prop :=
    forall addr,
      validAU (relaxedValidation a) (assumptionAndUpdateOfAddr a addr)
      /\ addr ∈ (map fst (newStates a)) -> addr ∈ (map fst (preTxAssumedState a)).

  Definition dummyEx : AssumptionExactness :=  {| min_balance := None; nonce_exact := true |}.

  Definition postTxActualBalNonce (assumedPreTxState : account_state) (assumEx: AssumptionExactness)  (speculativePostTxState: account_state)  (actualPreTxState: account_state) : (Z*Z) :=
        (actualPreTxState .^ _balance + (speculativePostTxState .^ _balance - assumedPreTxState .^ _balance),
         actualPreTxState  .^ _nonce + (speculativePostTxState .^ _nonce - assumedPreTxState .^ _nonce)).

  Definition dummyInc: Indices := {| block_index :=0; tx_index :=0 |}.
  Global Instance: LookupTotal address account_state StateOfAccounts :=
    fun a s => match s !! a with
               | Some f => f
               | None => dummyAc
               end.

(*
  Definition applyUpdates (p: PartialAccountState) (base: AccountM) : AccountM :=
    {
 *)

  
  Definition updateStorage (pre: option evm.storage) (updates: option AccountM) : evm.storage. Proof. Admitted.
  Definition accountFinalVal (relaxedValidation: bool) (au : TxAssumptionsAndUpdates) (actualPreTxState: option AccountM)  : option AccountM :=
    let assumEx := assumExactness (preAssumption au) in
    match  txUpdates au   with
    | None => actualPreTxState
    | Some (_, (_,txUpds)) =>
        match postTxState txUpds  with
        | None => None (* account did suicide if it existed *)
        | Some csUpdated =>
            let base := csUpdated &: _coreAc .@ _block_account_storage .= updateStorage (option_map (block.block_account_storage ∘ coreAc) actualPreTxState) (Some csUpdated) in
            if relaxedValidation then Some base else
              match preTxState (preAssumption au), actualPreTxState  with
              | Some csAssumed, Some csActual =>
                let assumEx := assumExactness (preAssumption au) in
                  Some(
                  let '(postTxBal, postTxNonce) := postTxActualBalNonce csAssumed assumEx csUpdated csActual in
                  let postAcState := if (isNone (min_balance assumEx)) then base else base &: _balance .= postTxBal in
                  if (nonce_exact assumEx) then postAcState else (postAcState &: _nonce .= postTxNonce))
              | _ , _ => Some base (* no relexed validation if either account is dead *)
              end
        end
    end.
        
  (* TODO: apply storage diffs 
  Definition accountFinalVal (relaxedValidation: bool) (orig : option (account_state* AssumptionExactness)) (actualPreTxState: AccountM) (upd: (ModelWithPtr (list AccountM))) : AccountM :=
    match snd upd, orig with
    | [], _ => actualPreTxState (* cannot happen. length upd = 1 *)
    | _, None => actualPreTxState (* cannot happen. if an address exists in the State::current_ map, it must exist in the State::preTxAssumedState map. *)
    | h::_, Some (assumedPreTxState, assumEx) =>
        let '(postTxBal, postTxNonce) := postTxActualBalNonce assumedPreTxState assumEx h (actualPreTxState) in
        if negb (relaxedValidation ) then h else
          let postAcState := if (isNone (min_balance assumEx)) then h else h &: _balance .= postTxBal in
          if (nonce_exact assumEx) then postAcState else (postAcState &: _nonce .= postTxNonce)
    end. *)

  (*
  Definition applyUpdate (relaxedValidation: bool) (orig : AssumptionAndUpdate) (actualPreTxState: StateOfAccounts) (acup: address * (ModelWithPtr (list AccountM))) :  StateOfAccounts :=
    let '(addr, upd) :=  acup in    
    <[addr := accountFinalVal relaxedValidation orig (actualPreTxState !!! addr) upd]> actualPreTxState.
  
  Definition applyUpdate (relaxedValidation: bool) (orig : option (account_state* AssumptionExactness)) (actualPreTxState: StateOfAccounts) (acup: address * (ModelWithPtr (list AccountM))) :  StateOfAccounts :=
    let '(addr, upd) :=  acup in    
    <[addr := accountFinalVal relaxedValidation orig (actualPreTxState !!! addr) upd]> actualPreTxState.
   *)

  Definition gmapMap {K V} `{Countable K} (f: K -> V -> option V) (g: gmap K V) : gmap K V. Proof. Admitted.
(*  Definition del {K V} `{Countable K} (k:K) (g: gmap K V) : gmap K V := delete k g. *)
  Definition applyUpdates (m: StateM) (preTxState: StateOfAccounts) :StateOfAccounts :=
    List.fold_left
      (fun ss upd => let addr := fst upd in
                     match assumptionAndUpdateOfAddr m addr with
                     | None => ss
                     | Some au =>
                         match accountFinalVal (relaxedValidation m) au (preTxState !! addr) with
                         | None => delete addr ss
                         | Some fv => <[ addr := fv ]> ss
                         end
                     end
      )
      (newStates m) preTxState.
  
  Definition execute_impl2_spec : WpSpec mpredI val val :=
    \arg{chainp :ptr} "chain" (Vref chainp)
    \prepost{(qchain:Qp) (chain: Chain)} chainp |-> ChainR qchain chain
    \arg{txp} "tx" (Vref txp)
    \prepost{qtx t} txp |-> TransactionR qtx t
    \arg{senderp} "sender" (Vref senderp)
    \prepost{qs} senderp |-> addressR qs (sender t)
    \arg{hdrp: ptr} "hdr" (Vref hdrp)
    \prepost{qh header} hdrp |-> BheaderR qh header
    \arg{block_hash_bufferp: ptr} "block_hash_buffer" (Vref block_hash_bufferp)
    \arg{statep: ptr} "state" (Vref statep)
    \pre{au: StateM} statep |-> StateR au
    \pre [| newStates au = []|] (* this is a weaker asumption than the impl, which also guarantees that preTxAssumedState only has the sender's account *)
    \prepost{(preBlockState: StateOfAccounts) (gl: BlockState.glocs) qb}
      (blockStatePtr au) |-> BlockState.Rfrag preBlockState qb gl
    \post{retp}[Vptr retp] Exists assumptionsAndUpdates result,
      statep |-> StateR assumptionsAndUpdates
      ** retp |-> ResultSuccessR EvmcResultR result 
       ** [| blockStatePtr assumptionsAndUpdates = blockStatePtr au |]
       ** [| indices assumptionsAndUpdates = indices au |]
      ** [| forall preTxState,
            satisfiesAssumptions assumptionsAndUpdates preTxState -> 
            let '(postTxState, actualResult) := stateAfterTransactionAux header preTxState (N.to_nat (tx_index (indices au))) t in
            postTxState = applyUpdates assumptionsAndUpdates preTxState /\ result = actualResult |].

  Definition execute_impl2_specg : WpSpec mpredI val val :=
    \with (speculative: bool) (* making this the first argument helps in proofs *)
     \arg{ctracerp} "" (Vref ctracerp)
    \arg{chainp :ptr} "chain" (Vref chainp)
    \prepost{(qchain:Qp) (chain: Chain)} chainp |-> ChainR qchain chain
    \arg{txp} "tx" (Vref txp)
    \prepost{qtx t} txp |-> TransactionR qtx t
    \arg{senderp} "sender" (Vref senderp)
    \prepost{qs} senderp |-> addressR qs (sender t)
    \arg{hdrp: ptr} "hdr" (Vref hdrp)
    \prepost{qh header} hdrp |-> BheaderR qh header
    \arg{block_hash_bufferp: ptr} "block_hash_buffer" (Vref block_hash_bufferp)
    \arg{statep: ptr} "state" (Vref statep)
    \pre{au: StateM} statep |-> StateR au
    \pre [| newStates au = []|] (* this is a weaker asumption than the impl, which also guarantees that preTxAssumedState only has the sender's account *)
    \prepost{(preBlockState: StateOfAccounts) (gl: BlockState.glocs) qb}
    (blockStatePtr au) |-> BlockState.Rfrag preBlockState qb gl
    \prepost{preTxState} (if speculative then emp else blockStatePtr au |-> BlockState.Rauth preBlockState gl preTxState)
    \post{retp}[Vptr retp] Exists assumptionsAndUpdates result,
      statep |-> StateR assumptionsAndUpdates
      ** retp |-> ResultSuccessR EvmcResultR result 
      ** [| blockStatePtr assumptionsAndUpdates = blockStatePtr au |]
      ** [| validStateM assumptionsAndUpdates |]
       ** [| indices assumptionsAndUpdates = indices au |]
       ** [| let postCond preTxState :=
               let '(postTxState, actualResult) := stateAfterTransactionAux header preTxState (N.to_nat (tx_index (indices au))) t in
               postTxState = applyUpdates assumptionsAndUpdates preTxState /\ result = actualResult in
             if speculative then 
               forall preTxState, satisfiesAssumptions assumptionsAndUpdates preTxState -> postCond preTxState
             else satisfiesAssumptions assumptionsAndUpdates preTxState /\ postCond preTxState                                                                                    
             |].


  cpp.spec "monad::BlockState::can_merge(monad::State&) const"
    as can_merge with ( fun (this:ptr) =>
     \arg{statep} "state" (Vptr statep) 
     \prepost{assumptionsAndUpdates} statep |-> StateR assumptionsAndUpdates
     \prepost{preBlockState invId preTxState} this |-> BlockState.Rauth preBlockState invId preTxState
     \post{b} [Vbool b] [| if b
                           then satisfiesAssumptions assumptionsAndUpdates preTxState
                           else Logic.True |]).

  cpp.spec "monad::BlockState::merge(const monad::State&)"
    as merge with (fun (this:ptr) =>
    \arg{statep} "state" (Vptr statep) 
    \prepost{assumptionsAndUpdates} statep |-> StateR assumptionsAndUpdates
    \pre{preBlockState invId preTxState} this |-> BlockState.Rauth preBlockState invId preTxState
    \pre [| satisfiesAssumptions assumptionsAndUpdates preTxState |]
    \post this |-> BlockState.Rauth preBlockState invId (applyUpdates assumptionsAndUpdates preTxState)).

  (* spec for speculative phase *)
  cpp.spec "monad::BlockState::read_storage(const evmc::address&, monad::Incarnation, const evmc::bytes32&)"
    as read_storage_spec with (fun (this:ptr) =>
      \prepost{preBlockState g q} this |-> BlockState.Rfrag preBlockState q g
      \arg{addressp} "address" (Vptr addressp)
      \arg{incp} "incarnation" (Vptr incp)
      \prepost{q indices} incp |-> IncarnationR q indices
      \arg{keyp} "key" (Vptr keyp)
      \post{retp:ptr} [Vptr retp] Exists anyvalue:N, retp |-> bytes32R 1 anyvalue). 

  Definition lookupStorage (s: StateOfAccounts) (addr: address) (key: N) (blockTxInd: Indices) : N. Proof. Admitted.

  
  (* spec for re-exec phase *)
  cpp.spec "monad::BlockState::read_storage(const evmc::address&, monad::Incarnation, const evmc::bytes32&)"
    as read_storage_spec_auth with (fun (this:ptr) =>
      \prepost{preBlockState g preTxState} this |-> BlockState.Rauth preBlockState g preTxState
      \arg{addressp} "address" (Vptr addressp)
      \prepost{q address} addressp |-> addressR q address
      \arg{incp} "incarnation" (Vptr incp)
      \prepost{q blockTxInd} incp |-> IncarnationR q blockTxInd
      \arg{keyp} "key" (Vptr keyp)
      \prepost{key:N} keyp |-> bytes32R q key
      \post{retp:ptr} [Vptr retp]  retp |-> bytes32R 1 (lookupStorage preTxState address key blockTxInd)). 

(* TODO: add spec of read_storage *)


  (* delete *)
  Definition StateConstr : ptr -> WpSpec mpredI val val :=
    fun (this:ptr) =>
      \arg{bsp} "" (Vref bsp)
      \arg{incp} "" (Vptr incp)
      \pre{q inc} incp |-> IncarnationR q inc 
      \post this |-> StateR {| blockStatePtr := bsp; indices:= inc; preTxAssumedState := []; newStates:= []; relaxedValidation := false|}.


  Definition WithdrawalR (q: cQp.t) (w: Withdrawal) : Rep. Proof. Admitted.
  Definition ConsensusBlockHeaderR (q: cQp.t) (w: ConsensusBlockHeader) : Rep. Proof. Admitted.
  Definition EmptyCallFramesR (q: cQp.t) : Rep. Proof. Admitted.
  
  Definition AnkerMapIterR (i: option N) (keyLoc valueLoc : ptr) : Rep. Proof. Admitted.
  (*
  structR
      "ankerl::unordered_dense::v4_1_0::segmented_vector<std::pair<evmc::address, monad::VersionStack<monad::AccountState>>, std::allocator<std::pair<evmc::address, monad::VersionStack<monad::AccountState>>>, 4096ul>::iter_t<0b>" 1. (* TODO: add ownership of fields *)
   *)

  cpp.spec "ankerl::unordered_dense::v4_1_0::segmented_vector<std::pair<evmc::address, monad::VersionStack<monad::AccountState>>, std::allocator<std::pair<evmc::address, monad::VersionStack<monad::AccountState>>>, 4096ul>::iter_t<0b>::operator!=<0b>(const ankerl::unordered_dense::v4_1_0::segmented_vector<std::pair<evmc::address, monad::VersionStack<monad::AccountState>>, std::allocator<std::pair<evmc::address, monad::VersionStack<monad::AccountState>>>, 4096ul>::iter_t<0b>&) const" as iter_neq_spec with
  (fun this: ptr =>
     \arg{otherp: ptr} "other" (Vref otherp)
     \prepost{(i1 i2: option N) k1 k2 v1 v2}
       this  |-> AnkerMapIterR i1 k1 v1
     ** otherp |-> AnkerMapIterR i2 k2 v2
     \post[Vbool (negb (bool_decide (i1 = i2 /\ k1=k2 /\ v1=v2)))] emp).

  cpp.spec "ankerl::unordered_dense::v4_1_0::segmented_vector<std::pair<evmc::address, monad::VersionStack<monad::AccountState>>, std::allocator<std::pair<evmc::address, monad::VersionStack<monad::AccountState>>>, 4096ul>::iter_t<0b>::~iter_t()" as iterd with
  (fun this: ptr =>
     \pre{i k v} this |-> AnkerMapIterR i k v
     \post emp
  ).

Definition AnkerMapSliceSpineR {K V:Type} (tykey tyval: type) (khash: K -> N) (* {eqd: EqDecision K} *)
           (krep : Qp -> K -> Rep) 
           (vrep : Qp -> V -> Rep) (* fraction needed as there can be multiple concrrent readers of the value *)
           (* CFrational vrep *)
           (key: K)
           (loc: option ptr)
  : Rep. Proof. Admitted.

Definition AnkerMapSliceR {K V:Type} (tykey tyval: type) (khash: K -> N) (* {eqd: EqDecision K} *)
           (krep : Qp -> K -> Rep) 
           (vrep : Qp -> V -> Rep) (* fraction needed as there can be multiple concrrent readers of the value *)
           (* CFrational vrep *)
           (key: K)
           (val: option (ModelWithPtr V))
  : Rep := AnkerMapSliceSpineR tykey tyval khash krep vrep key (option_map fst val)
             ** match val with
                | Some (loc, vall) => pureR (loc |-> vrep 1%Qp vall)
                | None => emp
                end.


   Definition current_end_spec_full : ptr -> WpSpec mpredI val val  :=
   (fun (this: ptr) =>
    \prepost{K V ktycpp vtycpp khash q (kR: Qp-> K->Rep) (vR : Qp -> V->Rep) m}
      this |->  AnkerMapR ktycpp vtycpp
           khash
           kR
           vR
           q
           m

    \post{(ret:ptr)}
      [Vptr ret]  ret |-> AnkerMapIterR None nullptr nullptr
  ).

(* end(): index = length l. TODO: generalize the method signature *)
cpp.spec
  "ankerl::unordered_dense::v4_1_0::detail::table<evmc::address, monad::VersionStack<monad::AccountState>, ankerl::unordered_dense::v4_1_0::hash<evmc::address, void>, std::equal_to<evmc::address>, std::allocator<std::pair<evmc::address, monad::VersionStack<monad::AccountState>>>, ankerl::unordered_dense::v4_1_0::bucket_type::standard, 1b>::end()"
  as current_end_spec
  with (fun (this: ptr) =>
    \prepost{K V ktycpp vtycpp khash (kR: Qp-> K->Rep) (vR : Qp -> V->Rep) k oloc}
      this |->  AnkerMapSliceSpineR ktycpp vtycpp
           khash
           kR
           vR
           k
           oloc

    \post{(ret:ptr)}
      [Vptr ret]  ret |-> AnkerMapIterR None nullptr nullptr
  ).

Definition ankerMapFind : ptr -> WpSpec mpredI val val  :=
  (fun (this: ptr) =>
    \arg{keyp: ptr} "key" (Vref keyp)
    \prepost{K V (q: Qp) ktycpp vtycpp khash (kR: Qp-> K->Rep) (vR : Qp -> V->Rep) m}
      this |->  AnkerMapR ktycpp vtycpp
           khash
           kR
           vR
           q
           m
    \prepost{qk k} keyp |-> kR qk k
    \post{(ret:ptr)}
    [Vptr ret] (Exists (found: bool),
      if found
      then (ret |-> AnkerMapIterR None nullptr nullptr ** [| k ∉ (map fst m)|])
      else Exists kloc vloc v i, 
              (ret |-> AnkerMapIterR (Some i) kloc vloc ** [| nth_error m (N.to_nat i) = Some (k, (vloc, v)) |])
    )
  ).
(* find(key): index matches position of key in l *)
cpp.spec
  "ankerl::unordered_dense::v4_1_0::detail::table<evmc::address, monad::VersionStack<monad::AccountState>, ankerl::unordered_dense::v4_1_0::hash<evmc::address, void>, std::equal_to<evmc::address>, std::allocator<std::pair<evmc::address, monad::VersionStack<monad::AccountState>>>, ankerl::unordered_dense::v4_1_0::bucket_type::standard, 1b>::find(const evmc::address&)"
  as current_find_spec
  with (fun (this: ptr) =>
    \arg{keyp: ptr} "key" (Vref keyp)
    \prepost{K V (q: Qp) ktycpp vtycpp khash (kR: Qp-> K->Rep) (vR : Qp -> V->Rep) k ovloc}
      this |->  AnkerMapSliceSpineR ktycpp vtycpp
           khash
           kR
           vR
           k
           ovloc
    \prepost{qk k} keyp |-> kR qk k
    \post{(ret:ptr)}
    [Vptr ret]  ret |->
        match ovloc with
        | None =>  AnkerMapIterR None nullptr nullptr
        | Some vloc => Exists kloc i,
            AnkerMapIterR (Some i) kloc vloc
        end
  ).

Definition pairOffsets (aty bty: type) (fst: bool) : offset :=
  _field (Nscoped (Ninst "std::pair" [Atype aty; Atype bty]) (Nid (if fst then "first":ident else "second":ident))).
      
Definition pairFstOffset (tykey tyval: type) : offset := pairOffsets tykey tyval true.
Definition pairSndOffset (tykey tyval: type) : offset := pairOffsets tykey tyval false.
Definition pairR {K V:Type} (tykey tyval: type)
           (krep : Qp -> K -> Rep) 
           (vrep : Qp -> V -> Rep) (q:Qp) (v: K*V) : Rep :=
  pairFstOffset tykey tyval |-> (vrep q (snd v)) **  pairSndOffset tykey tyval  |-> (vrep q (snd v)).
    cpp.spec
      "ankerl::unordered_dense::v4_1_0::segmented_vector<std::pair<evmc::address, monad::VersionStack<monad::AccountState>>,std::allocator<std::pair<evmc::address, monad::VersionStack<monad::AccountState>>>, 4096ul>::iter_t<0b>::operator->() const"
      as iter_arrow_spec
      with (fun this: ptr =>
        \prepost{i k v} this |-> AnkerMapIterR i k v
        \post{retp: ptr} [Vptr retp]  
        [| k = retp ,, pairFstOffset "evmc::address" "monad::VersionStack<monad::AccountState>" |]
        ** [| v = retp ,, pairSndOffset "evmc::address" "monad::VersionStack<monad::AccountState>" |]
           ).

  cpp.spec "monad::VersionStack<monad::AccountState>::recent()"
      as version_stack_recent_spec
        with (fun (this: ptr) =>
                \prepost{q h tl} this |-> VersionStackSpineR
                  "monad::AccountState"
                     (cQp.mut q)
                     (h::tl)
                     \post [Vptr  h] emp).

  Definition sliceInvariants (au: TxAssumptionsAndUpdates) : Prop :=
    let assumEx := assumExactness (preAssumption au) in
    let assumedPreTxState := preTxState (preAssumption au) in
    match  min_balance assumEx, txUpdates au   with
    | _, None => True
    | None , _ => True
    | Some minbal, Some (_, (_,txUpds)) =>
        match (postTxState txUpds), assumedPreTxState  with
        | None, _ => True
        | _, None => True
        | Some csUpdated, Some assumedPre =>
            incarnation csUpdated = incarnation assumedPre
            -> (assumedPre .^ _balance - csUpdated .^ _balance <= minbal) 
        end
    end.
End with_Sigma.
(*
Module Generalized1.
  Record State :=
    {
      assumptionsOnPreState: GlobalState -> Prop ;
      stateUpdates: GlobalState -> GlobalState;
      blockStatePtr: ptr;
    }.
  
  Context `{Sigma:cpp_logic} {CU: genv} {hh: HasOwn mpredI fracR}. (* some standard assumptions about the c++ logic *)
    Definition StateR (s: State): Rep. Proof. Admitted.

  Definition can_merge (this:ptr): WpSpec mpredI val val :=
    \prepost{(preState curState: StateOfAccounts) (block: Block)}
      this |-> BlockState.R block preState curState
    \arg{statep: ptr} "prev" (Vref statep)
    \pre{finalS}
      statep |-> StateR finalS
    \post{b} [Vbool b] if b then [|assumptionsOnPreState finalS curState|] else [| True |].
    
    
End Generalized1.
Module Generalized2.
  Class SplitGlobalState (Tcomm Trest: Type):=
    {
      isoL: (Tcomm * Trest) -> GlobalState;
      isoR: GlobalState -> (Tcomm * Trest);
      isIso: ssrfun.cancel isoL isoR;
    }.

  Context {Tcomm Trest: Type} {ss: SplitGlobalState Tcomm Trest}.

    Record State :=
    {
      assumptionsOnPreState: GlobalState -> Prop ;
      commStateUpdates: Tcomm -> Tcomm;
      restStateUpdates: Trest -> Trest;
      blockStatePtr: ptr;
    }.
    
End Generalized2.
(* demo:
- first spec: int x,y; void doubleXintoY()
- double(int & x, int & y) : arguments in specs 
- fork_task: skip the lambda struct part a bit. pass global vars to the task so that the lambda doesnt have a capture. one example to show both splitting 
- promise
- fork thread to show split ownership. do proof.

datastructures:
- arrays: sum spec, 2 kinds of splitting
- struct Point. void distance(Point & x). find cartesian geometry class in Coq
- (bonus, can skip )llist::rev: spec, why trust gallina rev: show lemmas
Proofs:
- uint64 gcd(uint64 x, uint64 y)
- llist::rev

offer docker image, homework (llist::apend, factorial),  and office hours.


day 2:

- Lock specs 
*)
*)


#[global] Opaque BlockHashBufferR.
#[global] Hint Opaque BlockHashBufferR: br_opacity.
#[global] Opaque BheaderR.
#[global] Hint Opaque BheaderR : br_opacity.
#[global] Opaque TransactionR.
#[global] Hint Opaque TransactionR : br_opacity.
#[global] Opaque StateR.
#[global] Hint Opaque StateR : br_opacity.
#[global] Hint Opaque AnkerMapPayloadsR : br_opacity.
#[global] Hint Opaque AnkerMapR : br_opacity.
#[global] Hint Opaque AnkerMapSpineR : br_opacity.
#[global] Hint Opaque AnkerMapPayloadsR : br_opacity.
#[only(lens)] derive StateM.

(* TODO: move to evmopsem *)
#[only(lens)] derive block.block_account.

