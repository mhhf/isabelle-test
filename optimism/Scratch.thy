theory Scratch
  imports Main
begin

type_synonym addr = nat

datatype iOVM_BondManager_State =
    NOT_COLLATALIZED
  | COLLATERALIZED
  | WITHDRAWING

record bond =
  state                :: iOVM_BondManager_State
  withdrawalTimestamp  :: nat

abbreviation initBond::bond where
  "initBond == (| state = NOT_COLLATALIZED, withdrawalTimestamp = 0 |)"

record rewards =
  canClaim             :: bool
  total                :: nat
  gasSpent             :: "(addr, nat) map"

abbreviation initRewards::rewards where
  "initRewards == (| canClaim = False, total = 0, gasSpent = Map.empty |)"

record ovm_bondManager_data =
  disputePeriodSeconds :: nat
  requiredCollateral   :: nat
  max                  :: nat
  owner                :: addr
  token                :: addr
  ovmFraudVerifier     :: addr
  bonds                :: "(addr, bond) map"
  witnessProviders     :: "(nat, rewards) map"

datatype transitionPhase =
    PRE_EXECUTION
  | POST_EXECUTION
  | COMPLETE

record ovm_stateTransitioner_data =
  preStateRoot         :: nat
  postStateRoot        :: nat
  stateTransitionIndex :: nat
  transitionHash       :: nat
  phase                :: transitionPhase

record ovm_fraudVerifier_data =
  transitioners        :: "(nat, addr) map"
abbreviation fraudVerifierInit    :: "ovm_fraudVerifier_data" where
  "fraudVerifierInit == (| transitioners = Map.empty |)"


datatype contract =
    OVM_BondManager ovm_bondManager_data
  | OVM_FraudVerifier ovm_fraudVerifier_data
  | OVM_StateTransitioner ovm_stateTransitioner_data

type_synonym contracts = "(addr, contract) map"

record state =
  bondManager           :: ovm_bondManager_data
  fraudVerifier         :: ovm_fraudVerifier_data
  stateTransitioners    :: "(nat, ovm_stateTransitioner_data) map"


(*
fun lookupp :: "contracts => addr => contract option" where
  "lookupp cs addr = cs addr"
  *)

abbreviation bondManagerAddr::addr where
  "bondManagerAddr == 4"
abbreviation fraudVerifierAddr::addr where
  "fraudVerifierAddr == 5"

abbreviation bondManagerDataInit::ovm_bondManager_data where
  "bondManagerDataInit == (|
    disputePeriodSeconds = 0,
    requiredCollateral   = 0,
    max                  = 0,
    owner                = 0,
    token                = 0,
    ovmFraudVerifier     = 5,
    bonds                = Map.empty,
    witnessProviders     = Map.empty
  |)"

abbreviation stateInit::state where
  "stateInit == (|
    bondManager        = bondManagerDataInit,
    fraudVerifier      = fraudVerifierInit,
    stateTransitioners = Map.empty
    |)"

(*
  TODO: only callable by the transitioner

      fraudVerifierAddress = (ovmFraudVerifier bondManagerData);
      fraudVerifierData = case cs fraudVerifierAddr of
          None                        => fraudVerifierInit
        | Some (OVM_FraudVerifier fvData) => fvData
        ;
*)
fun updateMap :: "('a, 'b) map => 'a => ('b => 'b) => ('a, 'b) map" where
  "updateMap mmap key f = (case mmap key of
      None     => mmap
    | Some val => mmap ++ [ key |-> f val ])"


fun recordGasSpent :: "nat => addr => nat => state => state" where
  "recordGasSpent ppreStateRoot wwho ggasSpent cs = (let
      doAddGasSpent = (%gasSpentWho. gasSpentWho + ggasSpent);
      updateRewards = (%rewards.(rewards (|
          total    := (total rewards) + ggasSpent,
          gasSpent := updateMap (gasSpent rewards) wwho doAddGasSpent
          |)
      ));
      updateBondManager = (%bondManagerData. bondManagerData (|
          witnessProviders := updateMap (witnessProviders bondManagerData) ppreStateRoot updateRewards
          |));
      newBondManager = updateBondManager (bondManager cs)
    in cs (| bondManager := newBondManager |))"


(* only fraud verifier can call this
  todo - error if no bond manager is found
*)
fun finalize :: "nat => nat => addr => nat => state => state" where
  "finalize ppreStateRoot bbatchIndex ppublisher ttimestamp cs = (let
      bondManagerData = (bondManager cs);
      claimable = (case (witnessProviders bondManagerData) ppreStateRoot of
          None => False
        | Some rrewards => canClaim rrewards
        );
      bond = (case (bonds bondManagerData) ppublisher of
          None   => initBond
        | Some x => x
        );
      wts = withdrawalTimestamp bond;
      bond_state = state bond;
      dps = disputePeriodSeconds bondManagerData;
      cond = wts ~= 0
           & wts > ttimestamp + dps
           & bond_state = WITHDRAWING
           ;
      newBond = bond (| state := if cond then bond_state else NOT_COLLATALIZED |);
      newBonds = (bonds bondManagerData) ++ [ ppublisher |-> newBond ];
      newBondManagerData = bondManagerData (| bonds := newBonds |);
      newState = cs (| bondManager := newBondManagerData |)
    in newState)"

fun deposit :: "addr => nat => state => state" where
  "deposit sender amount oldState = (let
    bondManagerData = bondManager oldState;
    bond = (case (bonds bondManagerData) sender of
        None   => initBond
      | Some x => x
      );
    newBond = bond (| state := COLLATERALIZED |);
    newBonds = (bonds bondManagerData) ++ [ sender |-> newBond ];
    newBondManagerData = bondManagerData (| bonds := newBonds |);
    newState = oldState (| bondManager := newBondManagerData |)
  in newState)"

fun startWithdrawal :: "addr => nat => state => state" where
  "startWithdrawal sender timestamp cs = (let
    bondManagerData = bondManager cs;
    bond = (case (bonds bondManagerData) sender of
        None   => initBond
      | Some x => x
      );
    ensureStateCollateralized = state bond = COLLATERALIZED;
    ensureStatePending = withdrawalTimestamp bond = 0;
    ensure = ensureStatePending & ensureStateCollateralized;
    newBond = bond (| state := WITHDRAWING, withdrawalTimestamp := timestamp |);
    newBonds = (bonds bondManagerData) ++ [ sender |-> newBond ];
    newBondManagerData = bondManagerData (| bonds := newBonds |);
    newState = cs (| bondManager := newBondManagerData |)
  in (if ensure then newState else cs))"

fun finalizeWithdrawal :: "addr => nat => state => state" where
  "finalizeWithdrawal sender timestamp cs = (let
    bondManagerData = bondManager cs;
    bond = (case (bonds bondManagerData) sender of
        None   => initBond
      | Some x => x
      );
    dps = disputePeriodSeconds bondManagerData;
    wts = withdrawalTimestamp bond;
    bond_state = state bond;
    ensureDisputePeriodeOver = timestamp >= wts + dps;
    ensureWithdrawing = bond_state = WITHDRAWING;
    ensure = ensureDisputePeriodeOver & ensureWithdrawing;
    newBond = bond (| state := NOT_COLLATALIZED, withdrawalTimestamp := 0 |);
    newBonds = (bonds bondManagerData) ++ [ sender |-> newBond ];
    newBondManagerData = bondManagerData (| bonds := newBonds |);
    newState = cs (| bondManager := newBondManagerData |)
  in if ensure then newState else cs)"

fun claim :: "addr => nat => state => state" where
  "claim sender ppreStateRoot cs = (let
    bondManagerData = bondManager cs;
    rewards = case (witnessProviders bondManagerData) ppreStateRoot of
        None => initRewards
      | Some x => x
      ;
    ensureCanClaim = canClaim rewards;
    rc = requiredCollateral bondManagerData;
    gs = case (gasSpent rewards) sender of
        None => 0
      | Some x => x
      ;
    t = total rewards;
    amount = (rc * gs) div (2 * t);
    newGasSpent = (gasSpent rewards) ++ [ sender |-> 0 ];
    newRewards = rewards (| gasSpent := newGasSpent |);
    newWitnessProviders = (witnessProviders bondManagerData) ++ [ ppreStateRoot |-> newRewards ];
    newBondManagerData = bondManagerData (| witnessProviders := newWitnessProviders |);
    ensure = ensureCanClaim;
    newState = cs (| bondManager := newBondManagerData |)
  in if ensure then newState else cs)"


export_code claim finalizeWithdrawal startWithdrawal deposit finalize updateMap recordGasSpent in Haskell module_name Example file_prefix example


end
