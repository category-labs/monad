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

#[only(lens)] derive block.block_account.
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


#[local] Open Scope Z_scope.
(*
Require Import EVMOpSem.evmfull. *)
Import cancelable_invariants.
  
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
    (Z.to_N (Zdigits.binary_value _ (block.tr_nonce tx))).
  Definition TransactionR (q:Qp) (tx: Transaction) : Rep :=
    structR "monad::Transaction" q **
      _field "monad::Transaction::nonce" |-> ulongR q (tx_nonce tx).

  #[global] Instance learnTrRbase: LearnEq2 TransactionR:= ltac:(solve_learnable).

  Definition u256R  (q:Qp) (n:N) : Rep. Proof. Admitted.
  Definition u256t : type := (Tnamed (Ninst (Nscoped (Nglobal (Nid "intx")) (Nid "uint")) [Avalue (Eint 256 "unsigned int")])).
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

Import namemap.
Import translation_unit.
Require Import List.
Import bytestring_core.
Require Import bluerock.auto.cpp.
Require Import bluerock.auto.cpp.specs.


Context  {MODd : exb.module ⊧ CU}.
  cpp.spec (Ninst
   "monad::execute_block(const monad::Chain&, monad::Block&, monad::BlockState&, const monad::BlockHashBuffer&, monad::fiber::PriorityPool&)"
   [Avalue (Eint 11 "enum evmc_revision")]) as exbb_spec with (execute_block_simpler).


  
  cpp.spec 
  "monad::reset_promises(unsigned long)" as reset_promises with
      ( \with (Transaction: Type)
        \arg{transactions: list Transaction} "n" (Vn (lengthN transactions))
       \pre{newPromisedResource}
           _global "monad::promises" |-> parrayR (Tnamed "boost::fibers::promise<void>") (fun i t => PromiseUnusableR) transactions
       \post Exists prIds, _global "monad::promises" |-> parrayR (Tnamed "boost::fibers::promise<void>") (fun i t => PromiseR (prIds i) (newPromisedResource i t)) transactions).
  
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


Definition resultT := Tnamed (resultn "monad::ExecutionResult").
Definition ExecutionResultR (tr: TransactionResult): Rep. Proof. Admitted.

Definition oResultT := (Tnamed (Ninst "std::optional" [Atype resultT])).

cpp.spec (Ninst "monad::execute_transactions(const monad::Block&, monad::fiber::PriorityPool&, const monad::Chain&, const monad::BlockHashBuffer&, monad::BlockState &)" [Avalue (Eint 11 "enum evmc_revision")]) as exect with (
    \arg{blockp: ptr} "block" (Vref blockp)
    \prepost{qb (block: Block)} blockp |-> BlockR qb block
    \pre [| lengthN (transactions block) < 2^64 - 1 |]%N
    \arg{priority_poolp: ptr} "priority_pool" (Vref priority_poolp)
    \prepost{priority_pool: PriorityPool} priority_poolp |-> PriorityPoolR 1 priority_pool
    \arg{chainp :ptr} "chain" (Vref chainp)
    \prepost{(qchain:Qp) (chain: Chain)} chainp |-> ChainR qchain chain
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


    cpp.spec (fork_task_nameg "monad::compute_senders(const monad::Block&, monad::fiber::PriorityPool&)::@0") as fork_task with (forkTaskSpec "monad::compute_senders(const monad::Block&, monad::fiber::PriorityPool&)::@0").

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
    \prepost{qs} senderp |-> optionAddressR qs (Some (sender t))
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

cpp.spec ((Ninst
             (Nscoped (Nglobal (Nid "monad"))
                (Nfunction function_qualifiers.N ("execute")
                   [Tref (Tconst (Tnamed (Nscoped (Nglobal (Nid "monad")) (Nid "Chain")))); "unsigned long"%cpp_type; Tref (Tconst (Tnamed (Nscoped (Nglobal (Nid "monad")) (Nid "Transaction"))));
                    Tref (Tconst (Tnamed (Ninst (Nscoped (Nglobal (Nid "std")) (Nid "optional")) [Atype (Tnamed (Nscoped (Nglobal (Nid "evmc")) (Nid "address")))])));
                    Tref (Tconst (Tnamed (Nscoped (Nglobal (Nid "monad")) (Nid "BlockHeader")))); Tref (Tconst (Tnamed (Nscoped (Nglobal (Nid "monad")) (Nid "BlockHashBuffer"))));
                    Tref (Tnamed (Nscoped (Nglobal (Nid "monad")) (Nid "BlockState"))); Tref (Tnamed (Ninst (Nscoped (Nscoped (Nglobal (Nid "boost")) (Nid "fibers")) (Nid "promise")) [Atype "void"]))]))
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
  Record Indices :=
    {
      block_index: N;
      tx_index: N;
    }.

  Record AssumptionExactness :=
    {
      min_balance: option N; (* None means exact validation *)
      nonce_exact: bool;
    }.
      
      
  Record AssumptionsAndUpdates (* StateM *) :=
    {
      relaxedValidation: bool;
      original: gmap evm.address (evm.account_state * AssumptionExactness);
      newStates: gmap evm.address (list evm.account_state); (* head is the latest *)
      blockStatePtr: ptr;
      indices: Indices
    }.

Definition MapOriginalR
           (q: stdpp.numbers.Qp)
           (m: list 
                  (monad.proofs.evmopsem.evm.address *
                  (monad.proofs.evmopsem.evm.account_state
                   * AssumptionExactness)))
  : Rep :=
  structR
    "ankerl::unordered_dense::v4_1_0::detail::table<evmc::address, monad::AccountState, ankerl::unordered_dense::v4_1_0::hash<evmc::address, void>, std::equal_to<evmc::address>, std::allocator<std::pair<evmc::address, monad::AccountState>>, ankerl::unordered_dense::v4_1_0::bucket_type::standard, 1b>"
    (cQp.mut q).

(** 3) Rep for monad::State::current_ (table<address,VersionStack<AccountState>>) **)
Definition MapCurrentR
           (q: stdpp.numbers.Qp)
           (m: list
                  (monad.proofs.evmopsem.evm.address*
                  (list monad.proofs.evmopsem.evm.account_state)))
  : Rep :=
  structR
    "ankerl::unordered_dense::v4_1_0::detail::table<evmc::address, monad::VersionStack<monad::AccountState>, ankerl::unordered_dense::v4_1_0::hash<evmc::address, void>, std::equal_to<evmc::address>, std::allocator<std::pair<evmc::address, monad::VersionStack<monad::AccountState>>>, ankerl::unordered_dense::v4_1_0::bucket_type::standard, 1b>"
    (cQp.mut q).

(** 4) Rep for monad::State::logs_ (VersionStack<vector<Receipt::Log>>) **)
Definition LogsR (q: stdpp.numbers.Qp) : Rep :=
  structR
    "monad::VersionStack<std::vector<monad::Receipt::Log, std::allocator<monad::Receipt::Log>>>"
    (cQp.mut q).

(** 5) Rep for monad::State::code_ (table<bytes32,shared_ptr<CodeAnalysis>>) **)
Definition CodeMapR
           (q: stdpp.numbers.Qp)
           (cm: stdpp.gmap.gmap Corelib.Numbers.BinNums.N (* bytes32 as N *)
                             (list N)) 
  : Rep :=
  structR
    "ankerl::unordered_dense::v4_1_0::detail::table<evmc::bytes32, std::shared_ptr<evmone::baseline::CodeAnalysis>, ankerl::unordered_dense::v4_1_0::hash<evmc::bytes32, void>, std::equal_to<evmc::bytes32>, std::allocator<std::pair<evmc::bytes32, std::shared_ptr<evmone::baseline::CodeAnalysis>>>, ankerl::unordered_dense::v4_1_0::bucket_type::standard, 1b>"
    (cQp.mut q).

(** Helper to extract the newly‐deployed code map from the State model **)
Definition computeCodeMap
           (s : AssumptionsAndUpdates)
  : stdpp.gmap.gmap Corelib.Numbers.BinNums.N (list N) :=
  ∅.  (* TOFIXLATER: fold over s.newStates and extract code from each created account *)

  Definition IncarnationR (q:Qp) (i: Indices): Rep. Proof. Admitted.

(** Now lay out StateR.  We *no longer* re‐open the section here. **)
Definition StateR (s: AssumptionsAndUpdates) : Rep :=
   _field "monad::State::block_state_" |-> ptrR<"monad::BlockState"> 1$m (blockStatePtr s) ∗
   _field "monad::State::incarnation_" |-> IncarnationR 1$m%cQp (indices s) ∗
   _field "monad::State::original_" |-> MapOriginalR 1$m%cQp (map_to_list (original s)) ∗
   _field "monad::State::current_" |-> MapCurrentR 1$m%cQp (map_to_list (newStates s)) ∗
   _field "monad::State::logs_" |-> LogsR 1$m%cQp ∗ (* TOFIX: add a model arg to LogsR *)
   _field "monad::State::code_" |-> CodeMapR 1$m%cQp (computeCodeMap s) ∗
   _field "monad::State::version_" |-> uintR 1$m 0 ∗
   _field "monad::State::relaxed_validation_" |-> boolR 1$m (relaxedValidation s) ∗
   structR "monad::State" 1$m.  
  

  Definition nullifyBalNonce (e: evm.account_state) : evm.account_state. Proof. Admitted.
  (*    := {[ e with evm.account_balance := 0, evm.account_nonce:=0 ]}. *)
  
  (*
  Definition preImpl2 (blockStatePtr: ptr) (senderAddr: evm.address) (sender: account_state): AssumptionsAndUpdates:=
    {|
      blockStatePtr:= blockStatePtr;
      newStates:= ∅;
      original := <[senderAddr := sender]>∅;
    |}. *)
(*
  Definition EvmcResultR (r: TransactionResult): Rep. Proof. Admitted. *)

  Open Scope Z_scope.

  Definition zbvfun (fz: Z -> Z) (w: keccak.w256): keccak.w256:=
    let wnz := fz (Zdigits.binary_value _ w) in
    Zdigits.Z_to_binary _ wnz.
    
   
  Definition zbvlens {A:Type} (l: Lens A A keccak.w256 keccak.w256): Lens A A Z Z :=
    {| view := λ a : A, Zdigits.binary_value 256 (a .^ l);
      over := λ (fz : Z → Z) (a : A), (l %= zbvfun fz) a |}.
  Definition _balance : Lens evm.account_state evm.account_state Z Z:=
    zbvlens (_block_account_balance).
  Definition _nonce : Lens evm.account_state evm.account_state Z Z:=
    zbvlens (_block_account_nonce).
  
  Definition isNone {T} (a: option T):= negb (isSome a).
  Definition min_balanceN (a: AssumptionExactness) : N:=
    match min_balance a with
    | Some f => f
    | None => 0
    end.
      
      
  Definition satisfiesAssumptions (a: AssumptionsAndUpdates) (preTxState: StateOfAccounts) : Prop :=
    forall acAddr,
      match original a !! acAddr, preTxState !! acAddr  with
      | Some assumAcE, Some preTxAc =>
          let '(assumState, assumEx) := assumAcE in
          nullifyBalNonce assumState = nullifyBalNonce preTxAc
          /\ (if (negb (relaxedValidation a) || isNone (min_balance assumEx))
             then assumState .^ _balance = preTxAc .^ _balance
             else (min_balanceN assumEx <= preTxAc .^ _balance))
          /\ (if (negb (relaxedValidation a) || nonce_exact assumEx)
              then assumState .^ _nonce = preTxAc.^ _nonce
              else True)
      | None, None => True
      | _, _ => False                        
      end.
  Definition validAU (a: AssumptionsAndUpdates) : Prop :=
    forall acAddr,
      match original a !! acAddr  with
      | Some (assumState, assumEx) =>
          if ((relaxedValidation a) && isSome (min_balance assumEx))
          then (min_balanceN assumEx <= assumState .^ _balance) else True
      | None => True
      end.

  Definition dummyEx : AssumptionExactness :=  {| min_balance := None; nonce_exact := true |}.

  Definition postTxActualBalNonce (a: AssumptionsAndUpdates) addr (speculativePostTxState: account_state)  (actualPreTxState: account_state) : (Z*Z * AssumptionExactness) :=
    match original a !! addr with
    | None => (0,0, dummyEx) (* impossible *)
    | Some (assumedPreTxState, assumEx) =>
        (actualPreTxState .^ _balance + (speculativePostTxState .^ _balance - assumedPreTxState .^ _balance),
         actualPreTxState  .^ _nonce + (speculativePostTxState .^ _nonce - assumedPreTxState .^ _nonce), assumEx)
    end.

  Global Instance: LookupTotal address account_state StateOfAccounts :=
    fun a s => match s !! a with
               | Some f => f
               | None => block.block_account_default
               end.
                 
  Definition applyUpdate (a: AssumptionsAndUpdates) (actualPreTxState: StateOfAccounts) (acup: address * list account_state) :
    StateOfAccounts :=
    let '(addr, upd) :=  acup in
    match upd with
    | [] => actualPreTxState (* should not happen *)
    | h::_ =>
        let '(postTxBal, postTxNonce, assumEx) := postTxActualBalNonce a addr h (actualPreTxState !!! addr) in
        if negb (relaxedValidation a) then <[addr:=h]> actualPreTxState else
          let postAcState := if (isNone (min_balance assumEx)) then h else (h &: _balance .= postTxBal) in
          <[addr := if (nonce_exact assumEx) then postAcState else (postAcState &: _nonce .= postTxNonce)]> actualPreTxState
    end.

  Definition applyUpdates (a: AssumptionsAndUpdates) (preTxState: StateOfAccounts) :StateOfAccounts :=
    let ups := map_to_list (newStates a) in fold_left (applyUpdate a) ups preTxState.
  
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
    \pre{au: AssumptionsAndUpdates} statep |-> StateR au
    \pre [| newStates au = ∅ |] (* this is a weaker asumption than the impl, which also guarantees that original only has the sender's account *)
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
    \pre{au: AssumptionsAndUpdates} statep |-> StateR au
    \pre [| newStates au = ∅ |] (* this is a weaker asumption than the impl, which also guarantees that original only has the sender's account *)
    \prepost{(preBlockState: StateOfAccounts) (gl: BlockState.glocs) qb}
    (blockStatePtr au) |-> BlockState.Rfrag preBlockState qb gl
    \prepost{preTxState} (if speculative then emp else blockStatePtr au |-> BlockState.Rauth preBlockState gl preTxState)
    \post{retp}[Vptr retp] Exists assumptionsAndUpdates result,
      statep |-> StateR assumptionsAndUpdates
      ** retp |-> ResultSuccessR EvmcResultR result 
      ** [| blockStatePtr assumptionsAndUpdates = blockStatePtr au |]
      ** [| validAU assumptionsAndUpdates |]
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

  Definition bytes32R (q:Qp) (z:N) : Rep. Proof. Admitted.

  (* spec for speculative phase *)
  cpp.spec "monad::BlockState::read_storage(const evmc::address&, monad::Incarnation, const evmc::bytes32&)"
    as read_storage_spec with (fun (this:ptr) =>
      \pre{preBlockState g q} this |-> BlockState.Rfrag preBlockState q g
      \arg{addressp} "address" (Vptr addressp)
      \arg{incp} "incarnation" (Vptr incp)
      \prepost{q indices} incp |-> IncarnationR q indices
      \arg{keyp} "key" (Vptr keyp)
      \post{retp:ptr} [Vptr retp] Exists anyvalue:N, retp |-> bytes32R 1 anyvalue). 

  Definition lookupStorage (s: StateOfAccounts) (addr: address) (key: N) (blockTxInd: Indices) : N. Proof. Admitted.

  
  (* spec for re-exec phase *)
  cpp.spec "monad::BlockState::read_storage(const evmc::address&, monad::Incarnation, const evmc::bytes32&)"
    as read_storage_spec_auth with (fun (this:ptr) =>
      \pre{preBlockState g preTxState} this |-> BlockState.Rauth preBlockState g preTxState
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
      \post this |-> StateR {| blockStatePtr := bsp; indices:= inc; original := ∅; newStates:= ∅ ; relaxedValidation := false|}.


Definition w256_to_Z (w: monad.EVMOpSem.keccak.w256) : Corelib.Numbers.BinNums.Z :=
  monad.EVMOpSem.Zdigits.binary_value 256 w.

Definition w256_to_N (w: monad.EVMOpSem.keccak.w256) : Corelib.Numbers.BinNums.N :=
  Stdlib.ZArith.BinInt.Z.to_N (w256_to_Z w).

(* A simplistic layout of the "accessed_storage_" table: *)
Definition AccessedKeysR (q: stdpp.numbers.Qp)
           (keys: list Corelib.Numbers.BinNums.N)
  : bluerock.lang.cpp.logic.rep_defs.Rep :=
  anyR
    "ankerl::unordered_dense::v4_1_0::detail::table<evmc::bytes32, void, ankerl::unordered_dense::v4_1_0::hash<evmc::bytes32, void>, std::equal_to<evmc::bytes32>, std::allocator<evmc::bytes32>, ankerl::unordered_dense::v4_1_0::bucket_type::standard, 0b>"%cpp_type
    (cQp.mut q).

(* A simplistic layout of the "storage_" and "transient_storage_" tables: *)
Definition StorageMapR (q: stdpp.numbers.Qp)
           (m: monad.EVMOpSem.evm.storage)
  : bluerock.lang.cpp.logic.rep_defs.Rep :=
  anyR
    "ankerl::unordered_dense::v4_1_0::detail::table<evmc::bytes32, evmc::bytes32, ankerl::unordered_dense::v4_1_0::hash<evmc::bytes32, void>, std::equal_to<evmc::bytes32>, std::allocator<std::pair<evmc::bytes32, evmc::bytes32>>, ankerl::unordered_dense::v4_1_0::bucket_type::standard, 1b>"%cpp_type
    (cQp.mut q).

(* Compute a 256‐bit program‐length hash as an N *)
Definition code_hash_of_program
           (pr: monad.EVMOpSem.evm.program)
  : Corelib.Numbers.BinNums.N :=
  Stdlib.ZArith.BinInt.Z.to_N
    (monad.EVMOpSem.evm.program_length pr mod (2 ^ 256)%Z).


(* ------------------------------------------------------------------------- *)
(* 1) Bundle fields of AccountSubstate into a record                         *)
(* ------------------------------------------------------------------------- *)
Record AccountSubstateModel : Type := {
  asm_destructed     : bool;
  asm_touched        : bool;
  asm_accessed       : bool;
  asm_accessed_keys  : list Corelib.Numbers.BinNums.N
}.

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
           (ba: monad.EVMOpSem.block.block_account)
           (idx: Indices)
  : bluerock.lang.cpp.logic.rep_defs.Rep :=
  _field "monad::Account::balance"       |-> u256R q (w256_to_N ba.(monad.EVMOpSem.block.block_account_balance))
  ** _field "monad::Account::code_hash"  |-> bytes32R q (code_hash_of_program ba.(monad.EVMOpSem.block.block_account_code))
  ** _field "monad::Account::nonce"      |-> primR "unsigned long" (cQp.mut q) (w256_to_Z ba.(monad.EVMOpSem.block.block_account_nonce))
  ** _field "monad::Account::incarnation"|-> IncarnationR q idx
  ** structR "monad::Account"%cpp_name    (cQp.mut q).

(* ------------------------------------------------------------------------- *)
(* 4) AccountStateR: everything now fully defined                             *)
(* ------------------------------------------------------------------------- *)
Definition AccountStateR
           (q: stdpp.numbers.Qp)
           (orig:         monad.EVMOpSem.block.block_account)
           (asm:          AssumptionExactness)
           (idx:          Indices)
  : bluerock.lang.cpp.logic.rep_defs.Rep :=
  (* base substate *)
  _base "monad::AccountState"%cpp_name "monad::AccountSubstate"%cpp_name
    |-> AccountSubstateR q (Build_AccountSubstateModel false false false [])
  (* account_ via optionR *)
  ** _field "monad::AccountState::account_"
       |-> libspecs.optionR
            "monad::Account"%cpp_type
            (fun ba' => AccountR q ba' idx)
            q
            (if orig.(monad.EVMOpSem.block.block_account_exists)
             then Some orig else None)
  (* persistent storage_ *)
  ** _field "monad::AccountState::storage_"           |-> StorageMapR q (block.block_account_storage orig)
  (* transient storage_ *)
  ** (Exists transient_map, _field "monad::AccountState::transient_storage_" |-> StorageMapR q transient_map)
  (* exact‐nonce flag *)
  ** _field "monad::AccountState::validate_exact_nonce_"   |-> boolR (cQp.mut q) (nonce_exact asm)
  (* exact‐balance flag *)
  ** _field "monad::AccountState::validate_exact_balance_" |-> boolR (cQp.mut q)
                                                                  (Corelib.Init.Datatypes.negb
                                                                     (bool_decide (stdpp.option.is_Some (min_balance asm))))
  (* min_balance_ bound *)
  ** (match min_balance asm with
      | Corelib.Init.Datatypes.Some n =>
         _field "monad::AccountState::min_balance_" |-> u256R q n
      | Corelib.Init.Datatypes.None =>
         Exists (nb: Corelib.Numbers.BinNums.N),
           _field "monad::AccountState::min_balance_" |-> u256R q nb
      end)
  (* the struct itself *)
  ** structR "monad::AccountState"%cpp_name (cQp.mut q).
  
  
  (*
      \pre [| block.block_account_nonce senderAcState = block.tr_nonce t|]
     \post  [| match original assumptionsAndUpdates !! senderAddr with
            | Some senderAcState' => senderAcState'= senderAcState
            | _ => False
            end |]

*)  
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
