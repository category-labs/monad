Require Import monad.proofs.misc.
Require Import monad.proofs.libspecs.
Require Import monad.proofs.evmopsem.
Import linearity.
Require Import bluerock.auto.invariants.
Require Import bluerock.auto.cpp.proof.

Require Import bluerock.auto.cpp.tactics4.
Require Import monad.asts.block_state_cpp.
Require Import monad.proofs.exec_specs.
Disable Notation atomic_name'.
Set Printing FullyQualifiedNames.
Require Import Lens.Elpi.Elpi.
#[local] Open Scope lens_scope.

Section with_Sigma.
  Context `{Sigma:cpp_logic} {CU: genv}.
  Context  {MODd : ext.module ⊧ CU}.

  
(* Define `AccountStateR: cQp.t -> evm.account_state -> Rep`, the Rep predicate of the below C++ class `monad::AccountState`.
(all the c++ code below is in namespace `monad`)

```c++
class AccountState final : public AccountSubstate
{
public: // TODO
    template <class Key, class T>
    using Map = ankerl::unordered_dense::segmented_map<Key, T>;

    std::optional<Account> account_{};
    Map<bytes32_t, bytes32_t> storage_{};
    Map<bytes32_t, bytes32_t> transient_storage_{};
    bool validate_exact_nonce_{false};
    bool validate_exact_balance_{false};
    uint256_t min_balance_{0};

    evmc_storage_status zero_out_key(
        bytes32_t const &key, bytes32_t const &original_value,
        bytes32_t const &current_value);

    evmc_storage_status set_current_value(
        bytes32_t const &key, bytes32_t const &value,
        bytes32_t const &original_value, bytes32_t const &current_value);

public:
    explicit AccountState(std::optional<Account> &&account)
        : account_{std::move(account)}
    {
    }

    explicit AccountState(std::optional<Account> const &account)
        : account_{account}
    {
    }

    AccountState(AccountState &&) = default;
    AccountState(AccountState const &) = default;
    AccountState &operator=(AccountState &&) = default;
    AccountState &operator=(AccountState const &) = default;

    bytes32_t get_transient_storage(bytes32_t const &key) const
    {
        auto const it = transient_storage_.find(key);
        if (MONAD_LIKELY(it != transient_storage_.end())) {
            return it->second;
        }
        return {};
    }

    evmc_storage_status set_storage(
        bytes32_t const &key, bytes32_t const &value,
        bytes32_t const &original_value)
    {
        bytes32_t current_value = original_value;
        {
            auto const it = storage_.find(key);
            if (it != storage_.end()) {
                current_value = it->second;
            }
        }
        if (value == bytes32_t{}) {
            return zero_out_key(key, original_value, current_value);
        }
        return set_current_value(key, value, original_value, current_value);
    }

    void set_transient_storage(bytes32_t const &key, bytes32_t const &value)
    {
        transient_storage_[key] = value;
    }

    [[nodiscard]] bool validate_exact_nonce() const
    {
        return validate_exact_nonce_;
    }

    [[nodiscard]] bool validate_exact_balance() const
    {
        return validate_exact_balance_;
    }

    [[nodiscard]] uint256_t const &min_balance() const
    {
        return min_balance_;
    }

    void set_validate_exact_nonce()
    {
        validate_exact_nonce_ = true;
    }

    void set_validate_exact_balance()
    {
        validate_exact_balance_ = true;
    }

    void set_min_balance(uint256_t const &value)
    {
        if (value > min_balance_) {
            min_balance_ = value;
        }
    }
};
```
Defn of the base class:

```c++
class AccountState final : public AccountSubstate
{
public: // TODO
    template <class Key, class T>
    using Map = ankerl::unordered_dense::segmented_map<Key, T>;

    std::optional<Account> account_{};// what does None mean here?
    Map<bytes32_t, bytes32_t> storage_{};
    Map<bytes32_t, bytes32_t> transient_storage_{};
    bool validate_exact_nonce_{false};
    bool validate_exact_balance_{false};
    uint256_t min_balance_{0};// can we just use account_.value.balance for this? validate_exact_balance_ will determine whether it is an exact value or a lower bound

    evmc_storage_status zero_out_key(
        bytes32_t const &key, bytes32_t const &original_value,
        bytes32_t const &current_value);

    evmc_storage_status set_current_value(
        bytes32_t const &key, bytes32_t const &value,
        bytes32_t const &original_value, bytes32_t const &current_value);

public:
    explicit AccountState(std::optional<Account> &&account)
        : account_{std::move(account)}
    {
    }

    explicit AccountState(std::optional<Account> const &account)
        : account_{account}
    {
    }

    AccountState(AccountState &&) = default;
    AccountState(AccountState const &) = default;
    AccountState &operator=(AccountState &&) = default;
    AccountState &operator=(AccountState const &) = default;

    bytes32_t get_transient_storage(bytes32_t const &key) const
    {
        auto const it = transient_storage_.find(key);
        if (MONAD_LIKELY(it != transient_storage_.end())) {
            return it->second;
        }
        return {};
    }

    evmc_storage_status set_storage(
        bytes32_t const &key, bytes32_t const &value,
        bytes32_t const &original_value)
    {
        bytes32_t current_value = original_value;
        {
            auto const it = storage_.find(key);
            if (it != storage_.end()) {
                current_value = it->second;
            }
        }
        if (value == bytes32_t{}) {
            return zero_out_key(key, original_value, current_value);
        }
        return set_current_value(key, value, original_value, current_value);
    }

    void set_transient_storage(bytes32_t const &key, bytes32_t const &value)
    {
        transient_storage_[key] = value;
    }

    [[nodiscard]] bool validate_exact_nonce() const
    {
        return validate_exact_nonce_;
    }

    [[nodiscard]] bool validate_exact_balance() const
    {
        return validate_exact_balance_;
    }

    [[nodiscard]] uint256_t const &min_balance() const
    {
        return min_balance_;
    }

    void set_validate_exact_nonce()
    {
        validate_exact_nonce_ = true;
    }

    void set_validate_exact_balance()
    {
        validate_exact_balance_ = true;
    }

    void set_min_balance(uint256_t const &value)
    {
        if (value > min_balance_) {
            min_balance_ = value;
        }
    }
};
```
All the c++ code above are in the namespace `monad`

```c++
struct Account
{
    uint256_t balance{0}; // sigma[a]_b
    bytes32_t code_hash{NULL_HASH}; // sigma[a]_c
    uint64_t nonce{0}; // sigma[a]_n
    Incarnation incarnation{0, 0};

    friend bool operator==(Account const &, Account const &) = default;
};
```

Below are some existing Rep predicates that you can use:
- IncarnationR is the existing Rep predicate for the c++ class `monad::Incarnation`.
- bytes32R for `bytes32_t` (alias for `evmc::bytes32`).
- u256t for `uint256_t` (alias for `intx::uint<256>`)
- addressR is the Rep predicate for Address (alias for `evmc::address`)

Many of these Rep predicates are currently admitted. You dont need to define them. But their type will tell you the Gallina models of these typess.
Unfortunately, there is currently no way to search the Coq context for Rep predicate definitions/axioms for a given C++ type.
So, if a Rep predicate for a class has not been mentioned in this first prompt, you can assume it doesnt exist and you need to define it.
If you have not been shown the C++ body of the class whose Rep predicate you need, you can just admit it. But to do that you need to chose the type, especially the type of the Gallina (mathematical) model of the type. Choose wisely. When possible, consider multiple options and compare pros and cons.


+++ QUERIES

Print evm.account_state.
Print block.block_account.
Print IncarnationR.
Print addressR.
Print bytes32R.
Print u256R.
Check Zdigits.binary_value.
Check Zdigits.Z_to_binary.
*)
(* ---------------------------------------------------------------------- *)
(* Admitted helper Rep‐predicates for storage, program, bool, and w256.  *)
(* ---------------------------------------------------------------------- *)

Definition storageR
  (q : cQp.t)
  (st : monad.EVMOpSem.evm.storage)
  : bluerock.lang.cpp.logic.rep_defs.Rep.
Admitted. (* TOFIXLATER: implement Rep for keccak.w256 → keccak.w256 map *)

Definition programR
  (q  : cQp.t)
  (pr : monad.EVMOpSem.evm.program)
  : bluerock.lang.cpp.logic.rep_defs.Rep.
Admitted. (* TOFIXLATER: implement Rep for evm.program *)

Definition boolR
  (q : cQp.t)
  (b : bool)
  : bluerock.lang.cpp.logic.rep_defs.Rep.
Admitted. (* TOFIXLATER: implement Rep for C++ bool fields *)

Definition w256R
  (q : cQp.t)
  (w : monad.EVMOpSem.keccak.w256)
  : bluerock.lang.cpp.logic.rep_defs.Rep.
Admitted. (* TOFIXLATER: implement Rep for 256‐bit vectors *)

(* ---------------------------------------------------------------------- *)
(* Skeleton for AccountStateR: relates C++ monad::AccountState to the     *)
(* Coq model evm.account_state = block.block_account                     *)
(* (the body is admitted for now)                                         *)
(* ---------------------------------------------------------------------- *)

Definition AccountStateR
  (q    : cQp.t)
  (acct : monad.proofs.evmopsem.evm.account_state)
  : bluerock.lang.cpp.logic.rep_defs.Rep :=
  monad.proofs.libspecs.addressR q
    (monad.EVMOpSem.block.block_account_address acct)
  ∗
  storageR q
    (monad.EVMOpSem.block.block_account_storage acct)
  ∗
  programR q
    (monad.EVMOpSem.block.block_account_code acct)
  ∗
  w256R q
    (monad.EVMOpSem.block.block_account_balance acct)
  ∗
  w256R q
    (monad.EVMOpSem.block.block_account_nonce acct)
  ∗
  boolR q
    (monad.EVMOpSem.block.block_account_exists acct)
  ∗
  boolR q
    (monad.EVMOpSem.block.block_account_hascode acct).
* )









  Definition AccountStateR (q:Qp) (s: evm.account_state) : Rep. Proof. Admitted.
  Print addressR.
  cpp.spec "monad::BlockState::fix_account_mismatch(monad::State&, const evmc::address&, monad::AccountState&, const std::optional<monad::Account>&) const" as fix_spec with (fun this:ptr =>
   \prepost{preBlockState g au actualPreTxState} (blockStatePtr au) |-> BlockState.Rauth preBlockState g actualPreTxState
   \pre [| blockStatePtr au = this |]
   \arg{statep: ptr} "state" (Vref statep)
   \pre{au}  statep |-> StateR au
   \arg{addrp: ptr} "address" (Vref addrp)
   \prepost{qa fixee} addrp |-> addressR qa fixee
   \arg{origp: ptr} "original" (Vref origp)
   \pre{assumedFixeeState} origp |-> AccountStateR 1 assumedFixeeState
   \arg{actualp: ptr} "actual" (Vref actualp)
   \pre actualp |-> libspecs.optionR "monad::AccountState" (AccountStateR 1) 1 (actualPreTxState !! fixee)
   \post{satisfiesAssumptionsb:bool} [Vbool satisfiesAssumptionsb]
      [| satisfiesAssumptionsb <-> satisfiesAssumptions au actualPreTxState |] **
      if (negb satisfiesAssumptionsb)
      then statep |-> StateR au ** origp |-> AccountStateR 1 assumedFixeeState
      else                          
        Exists auf exactFixeeAssumption, statep |-> StateR auf
          ** origp |-> AccountStateR 1 exactFixeeAssumption
          ** [| relaxedValidation auf = false |]
          ** [| applyUpdates auf actualPreTxState = applyUpdates au actualPreTxState |]).

  Set Nested Proofs Allowed.
  Lemma observeState (state_addr:ptr) q t: 
    Observe (reference_to "monad::AccountState" state_addr)
            (state_addr |-> AccountStateR q t).
  Proof using. Admitted.

  Definition observeStateF r q t := @observe_fwd _ _ _ (observeState r q t).
  Hint Resolve observeStateF : br_opacity.
Ltac slauto := (slautot ltac:(autorewrite with syntactic equiv iff slbwd; try rewrite left_id; try solveRefereceTo)); try iPureIntro.
  
Lemma prf: denoteModule module |-- fix_spec.
Proof using.
  verify_spec'.
  slauto.
Abort.
(*
  Locate RepFor.
  Print rep.RepFor.C.
  go.
  slauto2
  iAssert (origp |-> structR "monad::AccountState" 1) as "?"%string. admit.
  admitRef
  go.
  
    go.
*)    
End with_Sigma.
