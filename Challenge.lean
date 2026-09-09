import Cslib.Foundations.Semantics.LTS.Basic
import Cslib.Foundations.Semantics.LTS.OmegaExecution

/-! Generated from the reviewed Peterson specifications, preserving their definitions.
The two targets state safety and conditional one-passage global progress. -/

/-!
# Peterson's two-process safety specification

This module is the authoritative Lean transcription of the accepted
one-passage, sequentially consistent model.  It declares the state, the twelve
atomic transition families, finite reachability, mutual exclusion, and the
reviewed strengthened invariant.  Proofs belong in separate modules.
-/

namespace Peterson

/-- The two processes, also used as the two possible values of `turn`. -/
inductive Proc where
  | p1
  | p2
  deriving DecidableEq, Repr

namespace Proc

/-- The process distinct from `i`. -/
def other : Proc → Proc
  | .p1 => .p2
  | .p2 => .p1

end Proc

/-- The fixed short-circuit operand order used by one transition system. -/
inductive WaitOrder where
  | flagFirst
  | turnFirst
  deriving DecidableEq, Repr

/-- Project-defined control positions for one displayed passage of Figure 1. -/
inductive PC where
  | beforeFlag
  | betweenWrites
  | beforeFirstRead
  | betweenReads
  | critical
  | beforeExitWrite
  | afterPassage
  deriving DecidableEq, Repr

/-- The two shared fields and the two private program counters. -/
structure State where
  flag : Proc → Bool
  turn : Proc
  pc : Proc → PC

namespace State

/-- Update one process's flag and leave every other state component unchanged. -/
def setFlag (s : State) (i : Proc) (value : Bool) : State :=
  { s with flag := Function.update s.flag i value }

/-- Update the shared turn value and leave every other component unchanged. -/
def setTurn (s : State) (value : Proc) : State :=
  { s with turn := value }

/-- Update one process's private control position. -/
def setPC (s : State) (i : Proc) (value : PC) : State :=
  { s with pc := Function.update s.pc i value }

end State

/--
An observable label records the actor, the shared location accessed, and the
value read or written.  `finishCritical` is the sole private-only boundary.
-/
inductive Action where
  | writeFlagTrue (actor : Proc)
  | writeTurn (actor value : Proc)
  | readFlag (actor observedProcess : Proc) (value : Bool)
  | readTurn (actor value : Proc)
  | finishCritical (actor : Proc)
  | writeFlagFalse (actor : Proc)
  deriving DecidableEq, Repr

/--
One atomic protocol action.  The four order-independent constructors encode
the two entry writes, the private critical-completion boundary, and the exit
write.  The other eight constructors are the four read outcomes for each
fixed short-circuit order.  There is no stutter or transition from
`afterPassage`.
-/
inductive Step (order : WaitOrder) : State → Action → State → Prop where
  | writeFlagTrue (hpc : s.pc i = .beforeFlag) :
      Step order s (.writeFlagTrue i)
        ((s.setFlag i true).setPC i .betweenWrites)
  | writeTurn (hpc : s.pc i = .betweenWrites) :
      Step order s (.writeTurn i i)
        ((s.setTurn i).setPC i .beforeFirstRead)
  | flagFirstReadFlagFalse
      (horder : order = .flagFirst)
      (hpc : s.pc i = .beforeFirstRead)
      (hflag : s.flag i.other = false) :
      Step order s (.readFlag i i.other false) (s.setPC i .critical)
  | flagFirstReadFlagTrue
      (horder : order = .flagFirst)
      (hpc : s.pc i = .beforeFirstRead)
      (hflag : s.flag i.other = true) :
      Step order s (.readFlag i i.other true) (s.setPC i .betweenReads)
  | flagFirstReadTurnOther
      (horder : order = .flagFirst)
      (hpc : s.pc i = .betweenReads)
      (hturn : s.turn = i.other) :
      Step order s (.readTurn i i.other) (s.setPC i .critical)
  | flagFirstReadTurnSelf
      (horder : order = .flagFirst)
      (hpc : s.pc i = .betweenReads)
      (hturn : s.turn = i) :
      Step order s (.readTurn i i) (s.setPC i .beforeFirstRead)
  | turnFirstReadTurnOther
      (horder : order = .turnFirst)
      (hpc : s.pc i = .beforeFirstRead)
      (hturn : s.turn = i.other) :
      Step order s (.readTurn i i.other) (s.setPC i .critical)
  | turnFirstReadTurnSelf
      (horder : order = .turnFirst)
      (hpc : s.pc i = .beforeFirstRead)
      (hturn : s.turn = i) :
      Step order s (.readTurn i i) (s.setPC i .betweenReads)
  | turnFirstReadFlagFalse
      (horder : order = .turnFirst)
      (hpc : s.pc i = .betweenReads)
      (hflag : s.flag i.other = false) :
      Step order s (.readFlag i i.other false) (s.setPC i .critical)
  | turnFirstReadFlagTrue
      (horder : order = .turnFirst)
      (hpc : s.pc i = .betweenReads)
      (hflag : s.flag i.other = true) :
      Step order s (.readFlag i i.other true) (s.setPC i .beforeFirstRead)
  | finishCritical (hpc : s.pc i = .critical) :
      Step order s (.finishCritical i) (s.setPC i .beforeExitWrite)
  | writeFlagFalse (hpc : s.pc i = .beforeExitWrite) :
      Step order s (.writeFlagFalse i)
        ((s.setFlag i false).setPC i .afterPassage)

/-- The source-close step relation stored directly in CSLib's `LTS`. -/
def petersonLTS (order : WaitOrder) : Cslib.LTS State Action where
  Tr := Step order

/-- Both flags are false and both processes precede their first entry write. -/
def Initial (s : State) : Prop :=
  (∀ i, s.flag i = false) ∧ (∀ i, s.pc i = .beforeFlag)

/-- Finite CSLib reachability from either source-permitted initial turn value. -/
def Reachable (order : WaitOrder) (s : State) : Prop :=
  ∃ s₀, Initial s₀ ∧ (petersonLTS order).CanReach s₀ s

/-- Control positions after the flag-setting write and before the exit write. -/
def Interested : Set PC := fun pc =>
  match pc with
  | .betweenWrites | .beforeFirstRead | .betweenReads | .critical
  | .beforeExitWrite => True
  | .beforeFlag | .afterPassage => False

/-- Control positions after the process's turn write and before the exit write. -/
def TurnWritten : Set PC := fun pc =>
  match pc with
  | .beforeFirstRead | .betweenReads | .critical | .beforeExitWrite => True
  | .beforeFlag | .betweenWrites | .afterPassage => False

/-- Control positions after a successful wait evaluation and before the exit write. -/
def PastWait : Set PC := fun pc =>
  match pc with
  | .critical | .beforeExitWrite => True
  | .beforeFlag | .betweenWrites | .beforeFirstRead | .betweenReads
  | .afterPassage => False

/-- Process `i`'s flag agrees with its interested control range. -/
def FlagAgrees (i : Proc) (s : State) : Prop :=
  s.pc i ∈ Interested → s.flag i = true

/--
While `i` is past its wait but before its exit flag write, a peer currently
after its turn write and before its exit flag write excludes `i` from being
the current turn value.
-/
def TurnExcludes (i : Proc) (s : State) : Prop :=
  s.pc i ∈ PastWait ∧ s.pc i.other ∈ TurnWritten → s.turn ≠ i

/-- The reviewed two-clause invariant, stated symmetrically for both processes. -/
def Invariant (s : State) : Prop :=
  ∀ i, FlagAgrees i s ∧ TurnExcludes i s

/-- Process `i` occupies its critical section exactly at `PC.critical`. -/
def InCritical (i : Proc) (s : State) : Prop :=
  s.pc i = .critical

/-- The two processes do not occupy their critical sections simultaneously. -/
def MutuallyExclusive (s : State) : Prop :=
  ¬ (InCritical .p1 s ∧ InCritical .p2 s)

/-- The protected first target proposition; its proof belongs in `Safety`. -/
def PetersonMutualExclusion : Prop :=
  ∀ order s, Reachable order s → MutuallyExclusive s

end Peterson

/-!
# Protected one-passage progress contract

This module defines the one-passage temporal contract using CSLib infinite
executions over the source-specific observation adapter. It states validity,
participating-protocol fairness, critical completion, and the global future-entry
target. These are definitions, not a proof of progress. Correspondence and proofs
belong in separate modules.
-/

namespace Peterson

/-- Observation padding copies the whole state; an action is exactly `Step`. -/
def observationLTS (order : WaitOrder) : Cslib.LTS State (Option Action) where
  Tr s label t := match label with
    | none => t = s
    | some a => Step order s a t

/-- State and event observations, with no validity or fairness built into the type. -/
structure ProgressExecution where
  state : ℕ → State
  event : ℕ → Option Action

/-- Initiality allows either turn value; every tick is an observation transition. -/
def Valid (order : WaitOrder) (E : ProgressExecution) : Prop :=
  Initial (E.state 0) ∧ (observationLTS order).OmegaExecution E.state E.event

/-- Actor argument, independent of the observed process or the value written/read. -/
def actor : Action → Proc
  | .writeFlagTrue i | .writeTurn i _ | .readFlag i _ _
  | .readTurn i _ | .finishCritical i | .writeFlagFalse i => i

/-- A request at tick `n` takes effect in state `n + 1`. -/
def Request (E : ProgressExecution) (i : Proc) (n : ℕ) : Prop :=
  E.event n = some (.writeFlagTrue i)

/-- A started request that has not entered its critical section. -/
def Pending (i : Proc) (s : State) : Prop :=
  s.pc i = .betweenWrites ∨ s.pc i = .beforeFirstRead ∨ s.pc i = .betweenReads

/-- Participating protocol positions, including the exit flag write. -/
def Protocol (i : Proc) (s : State) : Prop :=
  Pending i s ∨ s.pc i = .beforeExitWrite

/-- A new entry edge, excluding old critical occupancy and padding. -/
def Entry (E : ProgressExecution) (i : Proc) (n : ℕ) : Prop :=
  ∃ a, E.event n = some a ∧ actor a = i ∧
    (E.state n).pc i ≠ .critical ∧ (E.state (n + 1)).pc i = .critical

/-- Opaque critical work finishes, separately from the following exit write. -/
def Finish (E : ProgressExecution) (i : Proc) (n : ℕ) : Prop :=
  E.event n = some (.finishCritical i)

/-- Some actor outcome is enabled at a participating protocol position. -/
def Enabled (order : WaitOrder) (i : Proc) (s : State) : Prop :=
  Protocol i s ∧ ∃ a t, actor a = i ∧ Step order s a t

/-- A participating actor step, with no requirement of a favorable read. -/
def Taken (E : ProgressExecution) (i : Proc) (n : ℕ) : Prop :=
  Protocol i (E.state n) ∧ ∃ a, E.event n = some a ∧ actor a = i

/-- Aggregate weak fairness on every suffix; optional initiation is excluded. -/
def ProtocolFair (order : WaitOrder) (E : ProgressExecution) : Prop :=
  ∀ i m, (∀ k, m ≤ k → Enabled order i (E.state k)) →
    ∃ n, m ≤ n ∧ Taken E i n

/-- Every critical occupant eventually finishes its opaque critical work. -/
def CriticalCompletes (E : ProgressExecution) : Prop :=
  ∀ i m, (E.state m).pc i = .critical → ∃ n, m ≤ n ∧ Finish E i n

/--
The accepted global future-entry target. The witness actor need not be the
pending actor. Tick `n = m` is future entry from observation `m`; an entry at
`m - 1` cannot discharge the obligation. No progress proof is declared here.
-/
def PetersonGlobalProgress : Prop :=
  ∀ order E, Valid order E → ProtocolFair order E → CriticalCompletes E →
    ∀ m, (∃ i, Pending i (E.state m)) → ∃ j n, m ≤ n ∧ Entry E j n

end Peterson

namespace Peterson

/-- Registry target; the Solution supplies the authoritative proof. -/
theorem peterson_mutual_exclusion : PetersonMutualExclusion := by sorry

/-- Registry target; the Solution supplies the authoritative proof. -/
theorem peterson_global_progress : PetersonGlobalProgress := by sorry

end Peterson
