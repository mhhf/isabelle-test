theory Scratch
  imports Main "HOL-Library.Mapping"
begin

fun reverse :: "'a list => 'a list" where
  "reverse [] = []" |
  "reverse (x # xs) = reverse xs @ [x]"

value "reverse [1::nat, 2, 3]"

value "reverse (a # xs)"

lemma rev1: "reverse (xs @ [a]) = a # reverse xs"
  apply(induct xs)
  apply auto
  done

theorem "reverse (reverse xs) = xs"
  apply(induct xs)
  apply auto
  by (simp add:rev1)

type_synonym word = nat
type_synonym addr = nat
type_synonym buffer = "nat list"
type_synonym contract = buffer

record frameState =
   contract     :: addr
   codeContract :: addr
   code         :: buffer
   pc           :: nat
   stack        :: "nat list"
   memory       :: buffer
   memorySize   :: nat
   calldata     :: buffer
   callvalue    :: nat
   caller       :: addr
   gas          :: nat
   returndata   :: buffer
   static       :: bool

record subState =
  selfdestructs   :: "addr list"
  touchedAccounts :: "addr list"

(*  refunds         :: "(addr, word) list" *)


record creationContext =
    creationContextCodehash  :: word
    creationContextReversion :: "(addr, buffer) mapping"
    creationContextSubstate  :: subState

record callContext =
    callContextTarget    :: addr
    callContextContext   :: addr
    callContextOffset    :: word
    callContextSize      :: word
    callContextCodehash  :: word
    callContextAbi       :: "word option"
    callContextData      :: buffer
    callContextReversion :: "(addr, contract) mapping"
    callContextSubState  :: subState

datatype frameContext =
    CallContext "callContext"
  | CreationContext "creationContext"


record frame =
  frameContext   :: frameContext
  frameState     :: frameState

datatype storageModel = ConcreteS | SymbolicS | InitialS

record env =
  contracts    :: "(addr, contract) mapping"
  chainId      :: word
  storageModel :: storageModel
  sha3Crack    :: "(word, buffer) mapping"

(*  keccakUsed   :: [([SWord 8], SWord 256)] *)


record block =
  coinbase    :: addr
  timestamp   :: word
  number      :: word
  difficulty  :: word
  gaslimit    :: word
  maxCodeSize :: word
(*  schedule    :: feeSchedule word*)


record txState =
  gasprice        :: word
  txgaslimit      :: word
  origin          :: addr
  toAddr          :: addr
  val             :: word
  substate        :: subState
  isCreate        :: bool
  txReversion     :: "(addr, contract) mapping"


datatype error
  = BalanceTooLow word word
  | UnrecognizedOpcode word
  | SelfDestruction
  | StackUnderrun
  | BadJumpDestination
  | Revert buffer
  | NoSuchContract addr
  | OutOfGas word word
  | BadCheatCode "word option"
  | StackLimitExceeded
  | IllegalOverflow
  | StateChangeWhileStatic
  | InvalidMemoryAccess
  | CallDepthLimitReached
  | MaxCodeSizeExceeded word word
  | PrecompileFailure
  | UnexpectedSymbolicArg
  | DeadPath

datatype vmResult
  = VMFailure error
  | VMSuccess buffer

datatype log = Log addr buffer "word list"

record vm =
  result         :: "vmResult option"
  state          :: frameState
  env            :: env
  block          :: block
  tx             :: txState
  logs           :: "log list"
  burned         :: word


end
